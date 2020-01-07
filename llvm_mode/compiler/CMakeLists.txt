
add_executable(TSYMClang tsym_clang.c)
set_target_properties(TSYMClang PROPERTIES OUTPUT_NAME "tsym-clang")

add_custom_command(TARGET TSYMClang POST_BUILD
    COMMAND ln -sf "tsym-clang" "tsym-clang++")
install (TARGETS TSYMClang DESTINATION ${ANGORA_BIN_DIR})
install (FILES ${CMAKE_CURRENT_BINARY_DIR}/tsym-clang++ DESTINATION ${ANGORA_BIN_DIR})
