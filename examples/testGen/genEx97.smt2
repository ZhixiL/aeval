(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (+ (+ (/ x1 3) (* 4 x4)) (* 5 x3)) (* (- 5) x2)) 3 ) (/ y 3))
) (
>= (* 3 y) (+ (+ (* 4 x2) (* 5 x1)) 3 )
)) (and (
> (/ y 2) (+ (+ (+ (+ (* (- 3) x1) (* (- 5) x3)) (/ x4 4)) (* (- 4) x2)) 4 )
) (
< (+ (+ (/ x1 3) (/ x2 2)) 4 ) (* 3 y)
))
))
