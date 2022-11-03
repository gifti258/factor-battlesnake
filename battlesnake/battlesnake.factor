USING: accessors arrays assocs furnace.actions furnace.json
hashtables http http.server http.server.dispatchers io.servers
json.reader kernel math math.order math.vectors namespaces
path-finding random sets sequences sequences.extras
sequences.product sorting ;
IN: battlesnake

: 2of ( json a b -- v ) [ of ] bi-curry@ bi 2array ;
: pos ( json -- pos ) "x" "y" 2of ;
: my-head ( json -- pos ) "you" of "head" of pos ;

: <info-action> ( -- action )
    <action> [ H{
        { "apiversion" "1" } { "color" "#002080" }
        { "head" "all-seeing" } { "tail" "mlh-gene" }
    } <json-content> ] >>display ;

CONSTANT: moves {
    { { 1 0 } "right" } { { 0 1 } "up" }
    { { -1 0 } "left" } { { 0 -1 } "down" }
}

TUPLE: snake id length health body ;
C: <snake> snake

:: (score-moves) ( snake-id hazard-damage wrapped? dim food
    hazards snakes depth -- scores )
    snakes [
        [ 1 - ] change-health
        dup [ body>> length ] [ length>> 1 - ] bi min
        '[ _ head ] change-body
    ] map [ [
        moves keys [ swap clone [
            tuck first v+ dim wrapped? [ [ rem ] 2map ] [ [
                [ 1 - 0 swap between? ] 2all?
            ] keepd and ] if prefix
        ] change-body ] with [ body>> first ] map-filter
    ] map ] [ [ body>> ] map union-all ] bi '[
        [ body>> first _ in? ] reject [
            dup body>> first [
                hazards '[ _ = ] count hazard-damage *
                '[ _ - ] change-health
            ] [ food in? [
                100 >>health [ 1 + ] change-length 
            ] when ] bi
        ] map [ health>> 0 <= ] reject
    ] map harvest <product-sequence> [
        [ id>> snake-id = ] find nip body>> first2 v-
    ] collect-by [ [
        [ body>> first ] collect-by values [ [
            dup [ length>> ] map supremum '[ length>> _ = ] one?
        ] [ [ length>> ] supremum-by ] bi and ] map sift
        dup [ [ id>> snake-id = ] partition
        [ length ] bi@ snakes length 1 - swap - 2array ] when
    ] map unzip [ supremum ] bi@ 2array ] assoc-map ;

: score-moves ( json -- scores )
    [ "you" of "id" of ]
    [ "game" of "ruleset" of
        [ "settings" of "hazardDamagePerTurm" of 0 or ]
        [ "name" of "wrapped" = ] bi ]
    [ "board" of
        [ "width" "height" 2of ]
        [ "food" "hazards" [ of [ pos ] map ] bi-curry@ bi ]
        [ "snakes" of [
            [ "id" "length" "health" [ of ] tri-curry@ tri ]
            [ "body" of [ pos ] map ] bi <snake>
        ] map ] tri
    ] tri 1 (score-moves) ;

: nearest-food ( json -- pos )
    [ my-head ] keep "board" of "food" of [ pos ] map
    [ drop f ]
    [ [ v- [ abs ] map-sum ] with infimum-by ] if-empty ;

TUPLE: find-food < astar json ;
: neighbors* ( pos -- seq ) moves keys [ v+ ] with map ;

M: find-food neighbors ( node astar -- seq )
    [ neighbors* ] dip json>> [
        [ "board" of "width" "height" 2of ] keep
        { "game" "ruleset" "name" } [ of ] each "wrapped" =
        [ [ [ rem ] 2map ] curry map ]
        [ [ [ 1 - 0 swap between? ] 2all? ] curry filter ] if
    ] [
        "board" of "snakes" of [ "body" of [ pos ] map ] map
        concat [ member? ] curry reject
    ] [
        "board" of "hazards" of [ pos ] map
        [ member? ] curry reject
    ] tri ;

M: find-food cost ( from to astar -- n ) 3drop 1 ;
M: find-food heuristic ( from to astar -- n ) 3drop 1 ;
: <find-food> ( json -- astar ) find-food new swap >>json ;

: <move-action> ( -- action )
    <action> [
        request get post-data>> data>> json>
        [ score-moves ] [
            [ my-head dup ]
            [ nearest-food ]
            [ <find-food> find-path ?second ] tri swap v-
        ] bi 2dup swap key? [ nip ] [
            drop >alist [ second ] supremum-by first
        ] if moves at "move" associate <json-content>
    ] >>submit ;

: run-battlesnake ( -- )
    <dispatcher>
        <info-action> "" add-responder
        <move-action> "move" add-responder
    main-responder set-global
    80 httpd wait-for-server ;

MAIN: run-battlesnake
