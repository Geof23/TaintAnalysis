file( GLOB SOURCES *.cpp )

INCLUDE_DIRECTORIES( ../../include )

add_library( ashwin_taint_a STATIC ${SOURCES} )
add_library( ashwin_taint_so SHARED ${SOURCES} )

set_target_properties( ashwin_taint_a
  PROPERTIES
  OUTPUT_NAME
  "ashwin_taint" )

set_target_properties( ashwin_taint_so
  PROPERTIES
  OUTPUT_NAME
  "ashwin_taint" )
