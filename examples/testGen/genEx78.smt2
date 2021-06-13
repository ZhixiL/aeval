(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (* 5 y) (+ (+ (+ (+ (* (- 3) x1) (/ x4 2)) (* (- 3) x3)) (/ x2 2)) 2 )
) (
= (/ y 3) (/ x1 4)
)) (
= (/ x1 2) (* 3 y)
)
))
