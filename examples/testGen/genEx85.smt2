(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
< (/ y 4) (+ (* 5 x1) (/ x2 2))
) (
< (* (- 3) y) (+ (+ (/ x3 3) (/ x2 3)) (* (- 3) x1))
)) (
not (= (/ y 3) (+ (/ x2 3) (* 3 x1)))
)
))