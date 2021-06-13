(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (/ x1 4) (* (- 5) x2)) (* 5 y))
) (
>= (+ (* 4 x1) (* 4 x2)) (* (- 3) y)
)) (
not (= (/ y 3) (+ (+ (* 3 x3) (/ x1 4)) (/ x2 2)))
)
))
