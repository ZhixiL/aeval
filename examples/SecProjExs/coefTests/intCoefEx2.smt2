(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (and (
  >= x2 (* y 2)
) (
  > (* 3 y) x1
)) (and (and (
  <= y x2
) (
  < x1 (* y 4)
)) (and (
  >= x2 (* 7 y)
) (
  <= (* 6 y) (+ x2 x1)
)))))
