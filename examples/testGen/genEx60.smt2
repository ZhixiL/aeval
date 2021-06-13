(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (+ (+ (* 3 x1) (/ x2 4)) (/ x3 2)) (/ y 4)
) (
< (+ (+ (+ (* 4 x3) (/ x1 4)) (/ x2 4)) (* (- 4) x4)) (/ y 3)
)) (
< (+ (/ x1 3) 4 ) (/ y 2)
)
))
