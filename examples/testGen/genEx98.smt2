(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
<= (+ (* 4 x1) (* (- 5) x2)) (/ y 3)
))