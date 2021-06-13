(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
= (+ (+ (+ (* 3 x1) (/ x2 3)) (/ x3 4)) 3 ) (* 3 y)
) (
< (/ y 2) (+ (+ (/ x3 4) (/ x1 3)) (* 4 x2))
)
))
