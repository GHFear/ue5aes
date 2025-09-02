// AES Key Scanner (Experimental)
// -------------------------------------------------
// Purpose:
//   Detects Type-2 AES key patterns used in Unreal Engine.
//
// Method:
//   Identifies functions that store 8 immediate constants 
//   into stack locals — a common signature for Type-2 
//   AES encryption keys in UE4/UE5 binaries.
//
// Compatibility:
//   Expected to work across Unreal Engine versions 
//   4.19 through 5.6.
//
// Author:
//   GHFear

#include <capstone/capstone.h>
#include <cstdint>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <thread>
#include <mutex>
#include <atomic>
#include <deque>
#include <algorithm>
#include <iomanip>
#include <unordered_set>
#include <chrono>

struct Config {
    size_t minUniqueStores = 8;
    bool   requirePrologue  = true;
    size_t maxFuncBytes     = 2048;
    size_t maxInstrs        = 512; 
    size_t backtrackBytes   = 64;
    size_t overlapBytes     = 128;
    size_t chunkSize        = 1 << 20;
    size_t progressPeriodMs = 200;
};

struct Match {
    size_t offset;
    size_t length;
    size_t funcStart;
};

struct MatchWithValues : public Match {
    std::vector<uint8_t> values;
};

static std::vector<uint8_t> readFile(const std::string& path) {
    std::ifstream f(path, std::ios::binary);
    if (!f) return {};
    return { std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>() };
}

#pragma pack(push,1)
struct IMAGE_DOS_HEADER_MIN { uint16_t e_magic; uint16_t _pad[29]; int32_t e_lfanew; };
struct IMAGE_FILE_HEADER_MIN { uint16_t Machine, NumberOfSections; uint32_t TimeDateStamp, PointerToSymbolTable, NumberOfSymbols; uint16_t SizeOfOptionalHeader, Characteristics; };
struct IMAGE_DATA_DIRECTORY_MIN { uint32_t VirtualAddress, Size; };
struct IMAGE_OPTIONAL_HEADER64_MIN {
    uint16_t Magic; uint8_t _pad1[14];
    uint64_t ImageBase;
    uint32_t SectionAlignment, FileAlignment; uint8_t _pad2[56];
    uint32_t NumberOfRvaAndSizes;
    IMAGE_DATA_DIRECTORY_MIN DataDirectory[16];
};
struct IMAGE_NT_HEADERS64_MIN { uint32_t Signature; IMAGE_FILE_HEADER_MIN FileHeader; IMAGE_OPTIONAL_HEADER64_MIN OptionalHeader; };
struct IMAGE_SECTION_HEADER_MIN { uint8_t Name[8]; union { uint32_t PhysicalAddress; uint32_t VirtualSize; } Misc; uint32_t VirtualAddress, SizeOfRawData, PointerToRawData, PointerToRelocations, PointerToLinenumbers; uint16_t NumberOfRelocations, NumberOfLinenumbers; uint32_t Characteristics; };
#pragma pack(pop)

static bool get_executable_regions_PE(const std::vector<uint8_t>& file, std::vector<std::pair<size_t,size_t>>& regions) {
    regions.clear();
    if (file.size() < sizeof(IMAGE_DOS_HEADER_MIN)) return false;
    auto* dos = reinterpret_cast<const IMAGE_DOS_HEADER_MIN*>(file.data());
    if (dos->e_magic != 0x5A4D) return false;
    size_t nt_off = static_cast<size_t>(dos->e_lfanew);
    if (nt_off + sizeof(IMAGE_NT_HEADERS64_MIN) > file.size()) return false;
    auto* nt = reinterpret_cast<const IMAGE_NT_HEADERS64_MIN*>(file.data() + nt_off);
    if (nt->Signature != 0x00004550) return false;
    const auto& fh = nt->FileHeader;
    size_t sec_off = nt_off + sizeof(uint32_t) + sizeof(IMAGE_FILE_HEADER_MIN) + fh.SizeOfOptionalHeader;
    if (sec_off + static_cast<size_t>(fh.NumberOfSections) * sizeof(IMAGE_SECTION_HEADER_MIN) > file.size()) return false;
    auto* sh = reinterpret_cast<const IMAGE_SECTION_HEADER_MIN*>(file.data() + sec_off);
    for (int i = 0; i < fh.NumberOfSections; ++i) {
        const bool exe = (sh[i].Characteristics & 0x20000000) != 0;
        if (exe && sh[i].PointerToRawData && sh[i].SizeOfRawData) {
            size_t off = sh[i].PointerToRawData;
            size_t sz  = sh[i].SizeOfRawData;
            if (off + sz <= file.size()) regions.emplace_back(off, sz);
        }
    }
    return !regions.empty();
}

static inline bool bytes_have_prologue(const std::vector<uint8_t>& buf, size_t off, size_t end) {
    if (off + 4 > end) return false;
    return buf[off] == 0x55 && buf[off+1] == 0x48 && buf[off+2] == 0x8B && buf[off+3] == 0xEC;
}

static inline bool safe_has_detail(const cs_insn* insn) { return insn && insn->detail; }

static inline bool is_stack_imm_dword_store(const cs_insn* insn) {
    if (!safe_has_detail(insn)) return false;
    if (insn->id != X86_INS_MOV) return false;
    const cs_x86& x = insn->detail->x86;
    if (x.op_count != 2) return false;
    const cs_x86_op& dst = x.operands[0];
    const cs_x86_op& src = x.operands[1];
    if (dst.type != X86_OP_MEM) return false;
    if (dst.size != 4) return false;
    if (dst.mem.base != X86_REG_RBP) return false;
    if (dst.mem.index != X86_REG_INVALID) return false;
    if (src.type != X86_OP_IMM) return false;
    if (src.size != 4) return false;
    return true;
}

static size_t find_prologue(const std::vector<uint8_t>& buf, size_t fileEnd, size_t matchOff, size_t backtrackLimit) {
    if (matchOff == 0) return 0;
    size_t start = (matchOff > backtrackLimit) ? (matchOff - backtrackLimit) : 0;
    for (size_t b = matchOff; b > start; --b) {
        size_t pos = b - 1;
        if (pos + 4 <= fileEnd && bytes_have_prologue(buf, pos, fileEnd)) return pos;
    }
    csh handle;
    if (cs_open(CS_ARCH_X86, CS_MODE_64, &handle) != CS_ERR_OK) return matchOff;
    cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);
    for (size_t b = matchOff; b > start; --b) {
        size_t pos = b - 1;
        cs_insn* insn = nullptr;
        size_t cnt = cs_disasm(handle, buf.data() + pos, std::min<size_t>(16, fileEnd-pos), 0x1000 + pos, 2, &insn);
        if (cnt >= 2 && safe_has_detail(insn)) {
            if (insn[0].id == X86_INS_PUSH && insn[1].id == X86_INS_MOV) {
                const cs_x86& x0 = insn[0].detail->x86;
                const cs_x86& x1 = insn[1].detail->x86;
                if (x0.op_count == 1 && x0.operands[0].type == X86_OP_REG && x0.operands[0].reg == X86_REG_RBP &&
                    x1.op_count == 2 && x1.operands[0].type == X86_OP_REG && x1.operands[0].reg == X86_REG_RBP &&
                    x1.operands[1].type == X86_OP_REG && x1.operands[1].reg == X86_REG_RSP) {
                    cs_free(insn, cnt);
                    cs_close(&handle);
                    return pos;
                }
            }
        }
        if (cnt) cs_free(insn, cnt);
    }
    cs_close(&handle);
    return matchOff;
}

struct Task { size_t start, end; };
class TaskQueue {
public:
    explicit TaskQueue(std::vector<Task>&& tasks) : q_(tasks.begin(), tasks.end()) {}
    bool pop(Task &t) { std::lock_guard<std::mutex> lk(m_); if (q_.empty()) return false; t = q_.front(); q_.pop_front(); return true; }
private:
    std::deque<Task> q_;
    std::mutex m_;
};

static void workerScanExtract(const std::vector<uint8_t>& buf,
                              TaskQueue& queue,
                              std::vector<MatchWithValues>& localOut,
                              std::atomic<size_t>& progressBytes,
                              const Config& cfg)
{
    csh handle;
    if (cs_open(CS_ARCH_X86, CS_MODE_64, &handle) != CS_ERR_OK) return;
    cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

    Task t;
    while (queue.pop(t)) {
        size_t start = t.start;
        size_t end   = std::min(t.end, buf.size());

        size_t off = start;
        while (off + 5 < end) {
            if (cfg.requirePrologue && !bytes_have_prologue(buf, off, end)) { 
                ++off; 
                progressBytes.fetch_add(1, std::memory_order_relaxed); 
                continue; 
            }

            size_t maxLen = std::min(cfg.maxFuncBytes, end - off);
            cs_insn* insn = nullptr;
            size_t cnt = cs_disasm(handle, buf.data() + off, maxLen, 0x1000 + off, cfg.maxInstrs, &insn);
            if (cnt == 0) { 
                ++off; 
                progressBytes.fetch_add(1, std::memory_order_relaxed); 
                continue; 
            }

            size_t funcBytes = 0;
            std::unordered_set<int64_t> uniqueDisps;
            std::vector<uint32_t> extracted;

            for (size_t i = 0; i < cnt && extracted.size() < 8; ++i) {
                funcBytes += insn[i].size;

                if (is_stack_imm_dword_store(&insn[i])) {
                    const cs_x86& x = insn[i].detail->x86;
                    uniqueDisps.insert(x.operands[0].mem.disp);

                    if (extracted.size() < 8)
                        extracted.push_back(static_cast<uint32_t>(x.operands[1].imm));
                }

                if (insn[i].id == X86_INS_RET) break;
                if (funcBytes >= maxLen) break;
            }

            if (uniqueDisps.size() >= cfg.minUniqueStores) {
                size_t funcStart = find_prologue(buf, off + funcBytes, off, cfg.backtrackBytes);
                
                std::vector<uint8_t> extractedBytes;
                for (auto val : extracted) {
                    for (int j = 0; j < 4; ++j)
                        extractedBytes.push_back((val >> (8 * j)) & 0xFF);
                }

                localOut.push_back({off, funcBytes, funcStart, extractedBytes});
                off += std::max<size_t>(funcBytes,1);
                progressBytes.fetch_add(funcBytes, std::memory_order_relaxed);
            } else { 
                ++off; 
                progressBytes.fetch_add(1, std::memory_order_relaxed); 
            }


            if (cnt) cs_free(insn, cnt);
        }
        if (off < end) progressBytes.fetch_add(end - off, std::memory_order_relaxed);
    }

    cs_close(&handle);
}

static void progressPrinter(std::atomic<size_t>& progress, size_t total, std::atomic<bool>& done, const Config& cfg) {
    using namespace std::chrono_literals;
    size_t last = (size_t)-1;
    while (!done.load(std::memory_order_acquire)) {
        size_t cur = progress.load(std::memory_order_relaxed);
        if (cur != last) {
            double pct = 100.0 * double(cur) / double(total ? total : 1);
            std::cout << "\rProgress: " << cur << "/" << total << " (" << std::fixed << std::setprecision(1) << pct << "%)   " << std::flush;
            last = cur;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(cfg.progressPeriodMs));
    }
    size_t cur = progress.load();
    double pct = 100.0 * double(cur) / double(total ? total : 1);
    std::cout << "\rProgress: " << cur << "/" << total << " (" << std::fixed << std::setprecision(1) << pct << "%)   \n";
}

std::vector<MatchWithValues> scanFunctionsMTExtract(const std::vector<uint8_t>& buf, const Config& cfg) {
    std::vector<std::pair<size_t,size_t>> regions;
    if (!get_executable_regions_PE(buf, regions)) regions.push_back({0, buf.size()});

    std::vector<Task> tasks;
    size_t totalBytes = 0;
    for (auto& r : regions) {
        size_t off = r.first;
        size_t end = off + r.second;
        totalBytes += r.second;
        for (size_t s = off; s < end; s += cfg.chunkSize) {
            size_t e = std::min(end, s + cfg.chunkSize);
            size_t s2 = (s == off) ? s : (s > cfg.overlapBytes ? s - cfg.overlapBytes : off);
            size_t e2 = (e == end) ? e : std::min(end, e + cfg.overlapBytes);
            tasks.push_back({s2,e2});
        }
    }

    TaskQueue queue(std::move(tasks));
    unsigned numThreads = std::thread::hardware_concurrency();
    if (numThreads == 0) numThreads = 4;

    std::vector<std::thread> workers;
    std::vector<std::vector<MatchWithValues>> localResults(numThreads);
    std::atomic<size_t> progressBytes{0};
    std::atomic<bool> donePrinter{false};

    std::thread printer(progressPrinter, std::ref(progressBytes), totalBytes, std::ref(donePrinter), cfg);

    for (unsigned i = 0; i < numThreads; ++i)
        workers.emplace_back(workerScanExtract, std::cref(buf), std::ref(queue), std::ref(localResults[i]), std::ref(progressBytes), cfg);

    for (auto &th : workers) th.join();
    donePrinter.store(true, std::memory_order_release);
    printer.join();

    std::vector<MatchWithValues> merged;
    for (auto &v : localResults) merged.insert(merged.end(), v.begin(), v.end());

    std::sort(merged.begin(), merged.end(), [](const MatchWithValues& a, const MatchWithValues& b){
        if (a.offset != b.offset) return a.offset < b.offset;
        return a.length > b.length;
    });

    std::vector<MatchWithValues> finalList;
    for (const auto &m : merged) {
        if (finalList.empty()) { finalList.push_back(m); continue; }
        auto &last = finalList.back();
        if (m.offset < last.offset + last.length) {
            if (m.length > last.length) last = m;
        } else finalList.push_back(m);
    }
    return finalList;
}

int main(int argc, char** argv) {
    std::ios::sync_with_stdio(false);
    if (argc < 2) { std::cerr << "Usage: " << argv[0] << " <binary>\n"; return 1; }

    Config cfg;
    if (argc >= 3) { try { cfg.minUniqueStores = std::stoul(argv[2]); } catch(...) {} }
    if (argc >= 4) { cfg.requirePrologue = (std::string(argv[3]) != "0"); }

    auto buf = readFile(argv[1]);
    if (buf.empty()) { std::cerr << "Failed to read file\n"; return 1; }

    auto results = scanFunctionsMTExtract(buf, cfg);

    if (results.empty()) { std::cout << "No candidates found.\n"; return 0; }

    std::cout << "Found " << results.size() << " candidate(s):\n";
    for (const auto &m : results) {
        std::cout << " FunctionStart=(0x" << std::hex << std::uppercase << m.funcStart << ")"
                  << " Potential AES Key=(0x";
        for (auto b : m.values) std::cout << std::hex << std::uppercase << std::setfill('0') << std::setw(2) << (int)b;
        std::cout << std::dec << ")\n";
    }

    return 0;
}
