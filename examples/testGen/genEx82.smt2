(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
not (= (* 5 y) (+ (* (- 4) x1) 3 ))
) (
<= (+ (+ (+ (/ x1 3) (/ x2 3)) (* 4 x3)) 2 ) (/ y 2)
)
))
