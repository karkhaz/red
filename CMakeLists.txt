cmake_minimum_required(VERSION 2.8)

SET (CMAKE_OSX_ARCHITECTURES "i386;x86_64" CACHE STRING  "Rogue")

project(red C)
set(RED_VERSION "2.2.0")

set(CPACK_PACKAGE_NAME "red")
set(CPACK_PACKAGE_CONTACT "László Nagy")
set(CPACK_PACKAGE_VENDOR ${CPACK_PACKAGE_CONTACT})
set(CPACK_PACKAGE_VERSION ${RED_VERSION})
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "BuildEAR")
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/COPYING")
set(CPACK_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")
set(CPACK_PACKAGING_INSTALL_PREFIX ${CMAKE_INSTALL_PREFIX})
set(CPACK_RPM_PACKAGE_RELEASE "1%{?dist}")
set(CPACK_RPM_PACKAGE_LICENSE "GPLv3")
set(CPACK_RPM_PACKAGE_GROUP "Development/Tools")
set(CPACK_RPM_PACKAGE_URL "http://github.com/rizsotto/Bear")
set(CPACK_RPM_PACKAGE_DESCRIPTION "Red is a tool to generate compilation database for clang tooling.")
set(CPACK_DEBIAN_PACKAGE_SHLIBDEPS ON)
include(CPack)

include(GNUInstallDirs)
install(FILES COPYING README.md ChangeLog.md
  DESTINATION ${CMAKE_INSTALL_DOCDIR})

include(CheckCCompilerFlag)
check_c_compiler_flag("-std=c99" C99_SUPPORTED)
if (C99_SUPPORTED)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c99")
endif()

add_definitions(-D_GNU_SOURCE)
list(APPEND CMAKE_REQUIRED_DEFINITIONS -D_GNU_SOURCE)

if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release")
endif()

set(RED_LIB_FILE ${CMAKE_SHARED_LIBRARY_PREFIX}red${CMAKE_SHARED_LIBRARY_SUFFIX})
set(DEFAULT_PRELOAD_FILE ${CMAKE_INSTALL_FULL_LIBDIR}/${RED_LIB_FILE})

add_subdirectory(libred)
add_subdirectory(red)
add_subdirectory(doc)
