
let-rec
  comp
    : [ A  : Type
      , x  : A
      , y  : A
      , z  : A
      , xy : x == y
      , yz : y == z
      ]   -> x == z
    = \A, x, y, z, xy, yz ->
      transport
        ( A
        , y
        , z
        , \x' -> x == x'
        , xy
        , yz
        )
in
  comp