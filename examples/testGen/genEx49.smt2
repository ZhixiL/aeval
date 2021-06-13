(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
<= (/ y 4) (+ (+ (/ x1 4) (/ x2 3)) (* 4 x3))
) (
= (/ y 3) (+ (/ x1 4) (* 4 x2))
)) (
= (* 3 y) (+ (+ (+ (* 4 x2) (* 5 x1)) (* 4 x3)) 1 )
)
))
