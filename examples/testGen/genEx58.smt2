(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (/ x1 3) (/ x2 3)) (/ x3 4)) (* 3 y))
) (
not (= (* (- 3) y) (+ (+ (+ (* (- 3) x3) (* (- 4) x1)) (* 5 x2)) 1 ))
)) (
<= (* 5 y) (* (- 4) x1)
)
))
