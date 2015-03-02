file( GLOB SOURCES *.cpp )


INCLUDE_DIRECTORIES( ../../include ../../../../../../src/LLVM/include ../../../../../../src/LLVM-build/include )

link_directories( ../../../../../../../bin/lib )

add_library( ashwin_taint_a STATIC ${SOURCES} )
add_library( ashwin_taint_so SHARED ${SOURCES} )

# target_link_libraries(ashwin_taint_a LLVMSupport ) #replaced this from LLVMCore for so and a
# target_link_libraries( ashwin_taint_so LLVMSupport )

install( FILES )

message( "in ${CMAKE_CURRENT_SOURCE_DIR}, CMAKE_CXX_FLAGS is ${CMAKE_CXX_FLAGS}" )

set_target_properties( ashwin_taint_a
  PROPERTIES
  OUTPUT_NAME
  "ashwin_taint" )

set_target_properties( ashwin_taint_so
  PROPERTIES
  OUTPUT_NAME
  "ashwin_taint" )
