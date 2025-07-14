
let-rec
  comp
    : [A : Type, x : A, y : A, z : A, xy : x == y, yz : y == z] -> x == z
    = \A, x, y, z, xy, yz ->
      transport(A, x, y, P, yz, xy)

  ; sym
    : [A : Type, x : A, y : A, xy : x == y] -> y == x
    = transport(A, x, y, P, refl, xy)
in
  comp