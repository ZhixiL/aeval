(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (+ (+ (+ (* (- 4) x1) (/ x4 3)) (* (- 4) x3)) (/ x2 3)) 3 ) (* (- 5) y)
) (
< (/ x1 3) (/ y 3)
)) (
< (+ (/ x2 3) (/ x1 4)) (/ y 4)
)
))
