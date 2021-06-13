(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
= (+ (/ x1 2) (/ x2 4)) (* (- 5) y)
) (
< (* (- 3) y) (+ (+ (* 5 x3) (* (- 4) x2)) (* (- 4) x1))
)
))
