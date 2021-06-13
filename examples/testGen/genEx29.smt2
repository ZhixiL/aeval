(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
>= (* 5 y) (+ (/ x1 2) 4 )
) (
<= (/ y 2) (+ (+ (+ (* 4 x1) (/ x2 2)) (* (- 5) x3)) 2 )
)) (and (
= (/ x1 3) (/ y 2)
) (
>= (+ (+ (/ x3 4) (/ x1 2)) (* (- 4) x2)) (* 3 y)
))
))
