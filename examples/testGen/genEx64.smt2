(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
not (= (+ (+ (+ (* (- 4) x1) (/ x4 3)) (/ x3 4)) (/ x2 4)) (/ y 3))
) (
>= (/ y 2) (+ (+ (/ x2 3) (* (- 4) x1)) (/ x3 2))
)
))
