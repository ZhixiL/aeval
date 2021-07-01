(assert (forall ((x1 Int) (x2 Int))
(exists ((y Int)) 
(and (and (
  >= (+ x1 x2) y
) (
  >= y (* 3 x2)
)) (and (
  < (* 2 y) x1
) (and (
  > y (- x1 2)
) (
  <= y (+ x2 7)
))))
)))