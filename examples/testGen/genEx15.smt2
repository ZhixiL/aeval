(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (* 4 x1) (* (- 4) x2)) (/ y 3))
) (
= (/ y 2) (+ (* (- 3) x1) (/ x2 2))
)) (
<= (* (- 4) x1) (/ y 2)
)
))
