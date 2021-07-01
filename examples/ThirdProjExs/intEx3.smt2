(assert (forall ((x1 Int) (x2 Int))
(exists ((y Int)) 
(and (
  >= (+ x1 x2) (* y 2)
) (
  > (* 4 y) x1
))
)))