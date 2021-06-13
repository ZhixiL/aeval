(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (/ y 4) (+ (/ x1 2) 3 )
) (
= (/ y 2) (+ (+ (+ (/ x1 3) (* 4 x4)) (* 5 x3)) (* 4 x2))
)) (and (
not (= (+ (+ (* (- 4) x2) (/ x1 4)) (/ x3 2)) (/ y 3))
) (
>= (/ y 2) (+ (+ (+ (/ x2 3) (* (- 5) x3)) (* 4 x1)) 3 )
))
))
