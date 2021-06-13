(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
<= (* (- 3) y) (+ (+ (+ (/ x1 2) (/ x4 4)) (* 3 x3)) (* (- 5) x2))
))
