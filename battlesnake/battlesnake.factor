USING: accessors arrays assocs assocs.extras combinators
furnace.actions furnace.json hashtables http http.server
http.server.dispatchers io.servers json.reader kernel logging
math math.order math.vectors namespaces pair-rocket path-finding
random sequences sequences.extras sequences.product sorting ;
IN: battlesnake

CONSTANT: config H{
    "apiversion" => "1"
    "color" => "#002080"
    "head" => "all-seeing"
    "tail" => "mlh-gene"
}

CONSTANT: moves H{
    { 0 +1 } => "up"
    { -1 0 } => "left"
    { 0 -1 } => "down"
    { +1 0 } => "right"
}

TUPLE: snake id length health body ;
C: <snake> snake

TUPLE: state dim food hazards id damage wrapped? ;
C: <state> state

: 2of ( json a b -- v ) [ of ] bi-curry@ bi 2array ;

: pos ( json -- pos ) "x" "y" 2of ;

: wrap-pos ( pos dim -- pos' ) [ rem ] 2map ; inline

: in-bounds? ( pos dim -- ? )
    [ 1 - 0 swap between? ] 2all? ; inline

: unique-supremum-by ( seq quot: ( elt -- x ) -- obj/f )
    [ 2dup map supremum '[ _ call( x -- x ) _ = ] one? ]
    [ supremum-by and ] 2bi ; inline

GENERIC: head ( obj -- pos )

M: assoc head "you" of "head" of pos ;

M: snake head body>> first ;

: move-damage ( snakes -- snakes' )
    [ [ 1 - ] change-health ] map ; inline

: shorten-tails ( snakes -- snakes' )
    [ [ 1 head* ] change-body ] map ; inline

: move-product ( snakes state -- snake-moves )
    [ moves keys ] dip [ wrapped?>> ] [ dim>> ] bi '[
        [ clone ] dip
        over head v+ _ [ _ wrap-pos ] when
        [ prefix ] curry change-body
    ] cartesian-map ; inline

: check-borders ( snake-moves state -- snake-moves' )
    [ wrapped?>> ] [ dim>> ] bi '[
        [ [ head _ in-bounds? ] filter ] map
    ] unless ; inline

: body-segments ( snakes -- body-segments )
    [ body>> ] map concat ; inline

: body-collisions ( snake-moves body-segments -- snake-moves' )
    '[ [ head _ member? ] reject ] map ; inline

: hazards ( snake-moves state -- snake-moves' )
    [ hazards>> ] [ damage>> ] bi '[
        [
            dup head _ [ = ] with count
            _ * [ - ] curry change-health
        ] map
    ] map ; inline

: food ( snake-moves state -- snake-moves' )
    food>> '[
        [
            _ dup member? [
                100 >>health
                [ 1 + ] change-length
            ] when
        ] map
    ] map ; inline

: out-of-health ( snake-moves -- snake-moves' )
    [ [ health>> 0 > ] filter ] map-harvest ; inline

: snake-product ( snake-moves state -- snake-product )
    [ <product-sequence> ] [ id>> ] bi* '[
        [ id>> _ = ] any?
    ] filter ; inline

: collate-moves ( snake-product state -- moves )
    id>> '[
        [ id>> _ = ] find nip body>> first2 v-
    ] collect-by ; inline

: head-collisions ( moves -- moves' )
    [
        [
            [ head ] collect-by values [
                [ length>> ] unique-supremum-by
            ] map-sift
        ] map
    ] assoc-map ; inline

: scores ( depth moves state -- scores )
    nipd id>> '[
        [
            [ id>> _ = ] partition [ length ] bi@ neg 2array
        ] map [
            unzip [ supremum ] bi@
        ] [
            [ [ first ] map-sum ] [ length ] bi /
        ] bi 3array
    ] assoc-map ; inline

: (score-moves) ( depth snakes state -- scores )
    {
        [ drop move-damage ]
        [ drop shorten-tails ]
        [
            [ [ move-product ] [ check-borders ] bi ]
            [ drop body-segments ] 2bi
        ]
        [ drop body-collisions ]
        [ hazards ]
        [ food ]
        [ drop out-of-health ]
        [ snake-product ]
        [ collate-moves ]
        [ drop head-collisions ]
        [ scores ]
    } cleave ; inline

: score-moves* ( json -- depth snakes state )
    1 swap [
        "board" of [
            "snakes" of [
                [
                    "id" "length" "health" [ of ] tri-curry@ tri
                ] [
                    "body" of [ pos ] map
                ] bi <snake>
            ] map
        ] [
            "width" "height" 2of
        ] [
            "food" "hazards" [ of [ pos ] map ] bi-curry@ bi
        ] tri
    ] [
        "you" of "id" of
    ] [
        "game" of "ruleset" of [
            "settings" of "hazardDamagePerTurn" of 0 or
        ] [
            "name" of "wrapped" =
        ] bi
    ] tri <state> ; inline

: score-moves ( json -- scores )
    score-moves* (score-moves) ; inline

TUPLE: find-food < astar json ;

: <find-food> ( json -- astar )
    find-food new swap >>json ; inline

M: find-food neighbors ( node astar -- seq )
    [ moves keys [ v+ ] with map ] dip json>> [
        [ "board" of "width" "height" 2of ] keep
        { "game" "ruleset" "name" } [ of ] each "wrapped" =
        [ '[ _ wrap-pos ] map ] [ '[ _ in-bounds? ] filter ] if
    ] [
        "board" of "snakes" of [
            "body" of 1 head* [ pos ] map
        ] map concat '[ _ member? ] reject
    ] bi ;

M: find-food cost ( from to astar -- n ) 3drop 1 ;

M: find-food heuristic ( from to astar -- n ) 3drop 1 ;

: nearest-food ( json -- seq )
    [ "board" of "food" of [ pos ] map ] [ head ] bi '[
        [ _ v- [ abs ] map-sum ] call( x -- x )
    ] sort-with ; inline

: handle-move ( json -- v )
    {
        [ head ]
        [ nearest-food ]
        [ ]
        [
            score-moves dup values ?supremum
            '[ _ = ] filter-values keys
        ]
    } cleave [
        '[
            _ <find-food> find-path ?first2 swap v-
            [ _ member? ] keep and
        ] with map-find drop
    ] keep swap dup [ nip ] [ drop random ] if ; inline

: <config-action> ( -- action )
    <action> [ config <json-content> ] >>display ;

: <move-action> ( -- action )
    <action> [
        request get post-data>> data>> "http.server" [
            dup \ <move-action> NOTICE log-message
        ] with-logging json> handle-move
        moves at "move" associate <json-content>
    ] >>submit ;

: run-battlesnake ( -- )
    <dispatcher>
        <config-action> "" add-responder
        <move-action> "move" add-responder
    main-responder set-global
    80 httpd wait-for-server ;

MAIN: run-battlesnake
