(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
= (+ (+ (+ (+ (/ x1 3) (* (- 3) x4)) (* 4 x3)) (* (- 5) x2)) 2 ) (/ y 2)
))
