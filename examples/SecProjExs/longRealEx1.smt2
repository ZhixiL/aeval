(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)

(assert (and(and(and(
  < y 12.3
) (and (
  > x5 x4
) (
  <= y x1
))) (and (and(
  >= y x2
) (
  >= y (* (- 3.1) x2)
)) (and(
  <= (* y 1.2) x1
) (
  > x3 y
)))) (and(and(
  < x1 x3
) (
  > y (- x1 2.1)
)) (and(
  <= y (+ x2 7.1)
) (
  <= (- x2 0.3) y
)))))