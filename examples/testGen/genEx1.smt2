(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (+ (* 4 x1) (* (- 4) x2)) (* 3 x3)) (/ y 3)
) (
= (+ (/ x1 2) (* (- 5) x2)) (* (- 5) y)
)) (and (
> (* 3 y) (+ (+ (/ x2 2) (* (- 4) x1)) 3 )
) (
< (+ (+ (+ (+ (/ x1 4) (* (- 3) x3)) (/ x4 2)) (/ x2 3)) 1 ) (/ y 3)
))
))
