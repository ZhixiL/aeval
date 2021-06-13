(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
not (= (* (- 3) y) (+ (+ (* 5 x1) (/ x2 3)) (/ x3 2)))
) (
= (+ (/ x1 3) 3 ) (/ y 4)
)
))
