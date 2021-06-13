(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (* (- 4) y) (+ (+ (+ (/ x1 2) (/ x4 2)) (* 3 x3)) (* 4 x2))
) (
> (* (- 4) y) (+ (/ x2 3) (* 3 x1))
)) (and (
= (/ y 3) (+ (+ (/ x1 4) (/ x2 3)) 1 )
) (
< (+ (* 3 x1) 1 ) (* 3 y)
))
))
