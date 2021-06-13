(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
not (= (* 5 y) (+ (/ x1 3) (/ x2 2)))
) (
<= (/ y 3) (* (- 4) x1)
)
))
