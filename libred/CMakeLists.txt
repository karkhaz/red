set(CMAKE_MACOSX_RPATH 1)

include(CheckFunctionExists)
include(CheckSymbolExists)
check_function_exists(execve HAVE_EXECVE)
check_function_exists(execv HAVE_EXECV)
check_function_exists(execvpe HAVE_EXECVPE)
check_function_exists(execvp HAVE_EXECVP)
check_function_exists(execvP HAVE_EXECVP2)
check_function_exists(execl HAVE_EXECL)
check_function_exists(execlp HAVE_EXECLP)
check_function_exists(execle HAVE_EXECLE)
check_function_exists(posix_spawn HAVE_POSIX_SPAWN)
check_function_exists(posix_spawnp HAVE_POSIX_SPAWNP)
check_symbol_exists(_NSGetEnviron crt_externs.h HAVE_NSGETENVIRON)

find_package(Threads REQUIRED)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/config.h.in ${CMAKE_CURRENT_BINARY_DIR}/config.h)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

add_library(red SHARED red.c)
target_link_libraries(red ${CMAKE_DL_LIBS})
if(THREADS_HAVE_PTHREAD_ARG)
    set_property(TARGET red PROPERTY COMPILE_OPTIONS "-pthread")
    set_property(TARGET red PROPERTY INTERFACE_COMPILE_OPTIONS "-pthread")
endif()
if(CMAKE_THREAD_LIBS_INIT)
    target_link_libraries(red "${CMAKE_THREAD_LIBS_INIT}")
endif()

set_target_properties(red PROPERTIES INSTALL_RPATH "@loader_path/${CMAKE_INSTALL_LIBDIR}")

include(GNUInstallDirs)
install(TARGETS red
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})
