(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
not (= (* (- 5) y) (+ (+ (+ (* 3 x1) (/ x2 3)) (/ x3 3)) 1 ))
))
