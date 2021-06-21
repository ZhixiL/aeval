(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)

(assert (and(and(and(
  < y 12
) (and (
  > x5 x4
) (
  <= y x1
))) (and (and(
  >= y x2
) (
  >= y (* (- 3) x2)
)) (and(
  <= (* y 1) x1
) (
  > x3 y
)))) (and(and(
  < x1 x3
) (
  > y (- x1 2)
)) (and(
  <= y (+ x2 7)
) (
  <= (- x2 1) y
)))))