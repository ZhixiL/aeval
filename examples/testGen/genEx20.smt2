(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (+ (* 4 x1) 2 ) (/ y 2)
) (
= (/ y 4) (+ (+ (/ x1 3) (* (- 4) x2)) 2 )
)) (and (
>= (/ y 4) (+ (/ x1 2) 4 )
) (
= (+ (+ (+ (* 4 x3) (* 3 x4)) (* (- 4) x2)) (* 4 x1)) (/ y 2)
))
))
