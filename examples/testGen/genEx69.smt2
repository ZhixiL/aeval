(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (+ (+ (* (- 5) x1) (* 3 x2)) (/ x3 3)) (* (- 3) y)
) (
<= (+ (+ (* 5 x1) (/ x2 3)) 1 ) (/ y 2)
)) (and (
>= (+ (+ (+ (/ x2 2) (/ x1 4)) (* 4 x3)) 4 ) (* (- 3) y)
) (
> (+ (+ (/ x2 2) (* (- 5) x1)) 3 ) (* 5 y)
))
))
