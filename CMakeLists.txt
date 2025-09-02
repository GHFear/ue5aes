cmake_minimum_required(VERSION 3.10)
project(ue5aes)

set(CMAKE_CXX_STANDARD 17)

find_package(Threads REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(CAPSTONE REQUIRED capstone)

add_executable(ue5aes main.cpp)
target_include_directories(ue5aes PRIVATE ${CAPSTONE_INCLUDE_DIRS})
target_link_libraries(ue5aes PRIVATE ${CAPSTONE_LIBRARIES} Threads::Threads)
