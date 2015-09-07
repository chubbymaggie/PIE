set(LLVM_LINK_COMPONENTS analysis support)
set(LLVM_USED_LIBS clangTooling clangAnalysis clangAST clangBasic clangStaticAnalyzerFrontend)

add_clang_executable(pinvgen
  tinyxml2.cpp
  string_utilities.cpp
  PredicateNode.cpp
  wp_computation.cpp
  abduction.cpp
  pinvgen.cpp
)

target_link_libraries(pinvgen
  clangTooling
  clangStaticAnalyzerFrontend
  clangAST
  clangBasic
)
