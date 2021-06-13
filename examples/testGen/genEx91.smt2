(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
not (= (* 3 y) (+ (+ (+ (* (- 4) x1) (* (- 4) x2)) (* (- 4) x3)) 1 ))
))
