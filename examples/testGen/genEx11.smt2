(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (/ x1 2) (/ y 3)
) (
not (= (+ (+ (+ (* (- 4) x1) (/ x2 4)) (/ x3 3)) 1 ) (* 3 y))
)) (
< (/ y 2) (+ (+ (* (- 3) x3) (* (- 3) x1)) (* 5 x2))
)
))
