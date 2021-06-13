(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
>= (* (- 3) y) (+ (/ x1 3) (* 3 x2))
) (
not (= (/ y 3) (+ (* (- 5) x1) (/ x2 3)))
)) (
= (+ (+ (+ (/ x3 3) (* (- 3) x1)) (* (- 5) x2)) (/ x4 3)) (* (- 3) y)
)
))
