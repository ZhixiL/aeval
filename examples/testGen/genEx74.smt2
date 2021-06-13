(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
< (+ (+ (+ (/ x1 2) (/ x4 3)) (/ x3 3)) (* 5 x2)) (* (- 5) y)
) (
not (= (* (- 5) y) (* (- 3) x1))
)
))
