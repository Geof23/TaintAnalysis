project( TaintAnalysis )
cmake_minimum_required(VERSION 3.0 FATAL_ERROR)

set ( TA_VERSION_MAJOR 0)
set ( TA_VERSION_MINOR 1)

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)

      message(STATUS "You can choose the type of build, options are:${build_types}")
      set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
          "Options are ${build_types}"
          FORCE
         )

      # Provide drop down menu options in cmake-gui
      set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")


include(CheckCXXCompilerFlag)

macro(add_cxx_flag_if_supported flagname)
	string( SUBSTRING ${flagname} 1 -1 newflag )
	message( "newflag is ${newflag}" )
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${newflag})

  if(HAVE_FLAG_${newflag})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
  endif()
endmacro()

if( CMAKE_BUILD_TYPE MATCHES "[a-zA-Z0-9]+Deb[a-zA-Z0-9]+" )
  add_cxx_flag_if_supported( "-g" )
endif()
if( CMAKE_BUILD_TYPE MATCHES "[a-zA-Z0-9]+Rel[a-zA-Z0-9]+" )
  add_cxx_flag_if_supported( "-O2" )
else()
  add_cxx_flag_if_supported( "-O0" )
endif()

add_cxx_flag_if_supported("-Wall")
#add_cxx_flag_if_supported("-Wextra")
add_cxx_flag_if_supported("-pedantic")
add_cxx_flag_if_supported("-Wunused")
add_cxx_flag_if_supported("-Wsign-compare")
add_cxx_flag_if_supported("-Wtype-limits")
add_cxx_flag_if_supported("-Wuninitialized")
add_cxx_flag_if_supported("-Wno-deprecated")
add_cxx_flag_if_supported("-Wstrict-aliasing")
add_cxx_flag_if_supported("-Wpointer-arith")
add_cxx_flag_if_supported("-Wheader-guard")
add_cxx_flag_if_supported("-fno-exceptions")
add_cxx_flag_if_supported("-fPIC")
add_cxx_flag_if_supported("-Woverloaded-virtual")
add_cxx_flag_if_supported("-Wcast-qual")
add_cxx_flag_if_supported("-pedantic")
add_cxx_flag_if_supported("-fno-rtti")
add_cxx_flag_if_supported("-Wno-unused_parameter")
add_cxx_flag_if_supported("-Wwrite-strings")


add_definitions("-D__STDC_LIMIT_MACROS -D__STDC_CONSTANT_MACROS -D_GNU_SOURCE")

add_subdirectory( lib )