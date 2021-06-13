(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (* 5 y) (+ (* 3 x1) (/ x2 2))
) (
= (+ (* (- 3) x1) 2 ) (* 3 y)
)) (
= (+ (+ (+ (/ x3 3) (* (- 5) x2)) (/ x1 2)) 4 ) (/ y 4)
)
))
