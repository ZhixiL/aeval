(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (* 3 y) (+ (+ (+ (/ x1 3) (/ x2 2)) (/ x3 3)) 1 )
) (
= (/ y 3) (* (- 4) x1)
)) (and (
> (* 3 y) (+ (/ x1 2) (/ x2 3))
) (
<= (* 5 y) (+ (+ (/ x2 4) (* 4 x1)) (* (- 3) x3))
))
))
