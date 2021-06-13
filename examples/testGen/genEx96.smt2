(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
not (= (/ y 2) (+ (+ (* 5 x1) (* (- 3) x2)) 3 ))
))
