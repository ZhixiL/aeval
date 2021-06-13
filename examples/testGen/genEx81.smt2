(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (/ x1 2) (/ x2 3)) (/ y 4)
) (
>= (/ y 3) (+ (* (- 3) x1) (/ x2 3))
)) (
not (= (+ (+ (+ (* 4 x3) (/ x1 4)) (/ x2 3)) (* (- 4) x4)) (* (- 5) y))
)
))
