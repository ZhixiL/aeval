(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
> (/ y 4) (+ (+ (* 3 x1) (* 3 x2)) (/ x3 4))
))
