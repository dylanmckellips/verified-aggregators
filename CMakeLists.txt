cmake_minimum_required(VERSION 3.10)
project(DegeneracyGraphAlgorithm)

set(CMAKE_CXX_STANDARD 17)

include_directories(include)

add_executable(degeneracy src/main.cpp)

# Add more source files as needed