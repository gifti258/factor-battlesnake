USING: accessors arrays assocs combinators furnace.actions
furnace.json hashtables http http.server http.server.dispatchers
io.servers json.reader kernel math math.parser math.order math.vectors
namespaces random path-finding sequences ;
IN: battlesnake

: <info-action> ( -- action ) <action> [ H{ { "apiversion" "1" } } <json-content> ] >>display ;
: 2of ( json a b -- v ) [ of ] bi-curry@ bi 2array ;
: pos ( json -- pos ) "x" "y" 2of ;
: head ( json -- pos ) "you" of "head" of pos ;
: board ( json -- dim ) "board" of "width" "height" 2of ;
: snakes ( json -- seq ) "board" of "snakes" of [ "body" of [ pos ] map ] map concat ;
: hazards ( json -- seq ) "board" of "hazards" of [ pos ] map ;
: neighbors* ( pos -- seq ) { { 0 1 } { 1 0 } { 0 -1 } { -1 0 } } [ v+ ] with map ;
: filter-border ( seq json -- seq' )
  dup { "game" "ruleset" "name" } [ of ] each "wrapped" =
  [ drop ] [ board [ [ 1 - 0 swap between? ] 2all? ] curry filter ] if ;
: filter-snakes ( seq json -- seq' ) snakes [ member? ] curry reject ;
: filter-hazards ( seq json -- seq' ) hazards [ member? ] curry reject ;
: legal-moves ( json -- seq )
  { [ head neighbors* ] [ filter-border ] [ filter-snakes ] [ filter-hazards ] } cleave ;
: pos>move ( v json -- assoc )
  head v- { { { 1 0 } "right" } { { -1 0 } "left" } { { 0 1 } "up" } { { 0 -1 } "down" } } at
  "move" associate ;
: nearest-food ( json -- pos )
  [ head ] keep "board" of "food" of [ pos ] map
  [ drop f ] [ [ v- [ abs ] map-sum ] with infimum-by ] if-empty ;
TUPLE: find-food < astar json ;
: <find-food> ( json -- astar ) find-food new swap >>json ;
M: find-food neighbors ( node astar -- seq )
  [ neighbors* ] dip json>> [ filter-border ] [ filter-snakes ] [ filter-hazards ] tri ;
M: find-food cost ( from to astar -- n ) 3drop 1 ;
M: find-food heuristic ( from to astar -- n ) 3drop 1 ;

: <move-action> ( -- action )
  <action> [
    request get post-data>> data>> json> [
      dup [ head ] [ nearest-food ] [ <find-food> ] tri
      find-path ?second [ nip ] [ legal-moves random ] if*
    ] keep pos>move <json-content>
  ] >>submit ;

: run-battlesnake ( -- )
  <dispatcher>
    <info-action> "" add-responder
    <move-action> "move" add-responder
  main-responder set-global
  8080 httpd wait-for-server ;
  
MAIN: run-battlesnake