(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (+ (+ (* 5 x1) (/ x4 3)) (* 3 x3)) (/ x2 4)) (/ y 2)
) (
< (/ y 4) (+ (+ (+ (/ x2 2) (/ x1 2)) (* (- 3) x3)) 3 )
)) (and (
>= (/ y 3) (+ (/ x1 2) 1 )
) (
>= (/ y 4) (+ (+ (* 5 x2) (/ x3 4)) (* 3 x1))
))
))
