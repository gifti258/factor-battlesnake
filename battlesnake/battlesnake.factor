USING: accessors arrays assocs assocs.extras combinators
furnace.actions furnace.json hashtables http http.server
http.server.dispatchers io io.servers json.reader kernel logging
math math.order math.statistics math.vectors namespaces
pair-rocket path-finding random sequences sequences.extras
sequences.product sets shuffle sorting ;
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

TUPLE: snake id health body ;
C: <snake> snake

TUPLE: state dim food hazards id damage wrapped? ;
C: <state> state

: 2of ( assoc a b -- v ) [ of ] bi-curry@ bi 2array ; inline

: pos ( assoc -- pos ) "x" "y" 2of ; inline

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
    [ hazards>> ] [ damage>> ] bi '[ [
        dup head _ [ = ] with count
        _ * [ - ] curry change-health
    ] map ] map ; inline

: food ( snake-moves state -- snake-moves' )
    food>> '[ [
        _ dup member? [
            100 >>health
        ] when
    ] map ] map ; inline

: out-of-health ( snake-moves -- snake-moves' )
    [ [ health>> 0 > ] filter ] map-harvest ; inline

: snake-product ( snake-moves state -- snake-product )
    [ <product-sequence> ] dip id>> '[
        [ id>> _ = ] any?
    ] filter ; inline

: collate-moves ( snake-product state -- moves )
    [ id>> ] [ dim>> ] bi '[
        [ id>> _ = ] find nip body>> first2 v-
        _ [ [ 2 + ] dip rem 2 - ] 2map
    ] collect-by ; inline

: head-collisions ( moves state -- moves' )
    id>> '[
        [
            dup [ head ] map all-unique? [ nip ] [
                [ head ] collect-by values [
                    [ body>> length ] unique-supremum-by
                ] map-sift [ id>> _ = ] none?
            ] if*
        ] filter
    ] assoc-map ; inline

DEFER: (score-moves)
: scores ( depth max-depth moves state -- scores )
    [ 1 + ] 3dip [ id>> ] keep over '[
        [
            [ clone ] map
            2pick <= over [ id>> _ = ] any? and [
                [ 2over ] dip _ (score-moves) values ?supremum
                [ { 0 -1/0. } ] unless*
            ] [
                [ id>> _ = ] partition
                [ [ health>> ] map-sum ] bi@ neg 2array
            ] if
        ] map unzip [ mean ] bi@ 2array
    ] assoc-map 2nip ;

: (score-moves) ( depth max-depth snakes state -- scores )
    [ move-damage shorten-tails ] dip {
        [
            [ [ move-product ] [ check-borders ] bi ] keepd
            body-segments body-collisions
        ]
        [ hazards ]
        [ food out-of-health ]
        [ snake-product ]
        [ collate-moves ]
        [ head-collisions ]
        [ scores ]
    } cleave ;

: score-moves* ( json -- depth max-depth snakes state )
    1 swap
    [ "board" of
        [ "snakes" of [ length 9 swap /i ] keep [
            [ "id" "health" [ of ] bi-curry@ bi ]
            [ "body" of [ pos ] map ] bi <snake>
        ] map ]
        [ "width" "height" 2of ]
        [ "food" "hazards" [ of [ pos ] map ] bi-curry@ bi ] tri
    ]
    [ "you" of "id" of ]
    [ "game" of "ruleset" of
        [ "settings" of "hazardDamagePerTurn" of 0 or ]
        [ "name" of "wrapped" = ] bi
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

M: find-food cost ( from to astar -- n )
    nipd json>> [ "board" of "hazards" of ] [ {
        "game" "ruleset" "settings"
        "hazardDamagePerTurn"
    } [ of ] each ] bi [ [ = ] with count ] dip * 1 + ;

M: find-food heuristic ( from to astar -- n ) 3drop 1 ;

: nearest-food ( json -- seq )
    [ "board" of "food" of [ pos ] map ] [ head ] bi '[
        [ _ v- [ abs ] map-sum ] call( x -- x )
    ] sort-with ; inline

: best-moves ( json -- vs )
    score-moves dup values ?supremum
    '[ _ = ] filter-values keys ; inline

: handle-move ( json -- v )
    {
        [ head ]
        [ nearest-food ]
        [ ]
        [ best-moves ]
    } cleave [
        '[
            _ <find-food> find-path ?first2 swap v-
            [ _ member? ] keep and
        ] with map-find drop
    ] keep over [ drop ] [ nip random ] if ; inline

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
    "ready" print flush
    80 httpd wait-for-server ;

MAIN: run-battlesnake
