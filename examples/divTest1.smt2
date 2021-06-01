(declare-fun y () Int)
(declare-fun x () Int)

(assert (and (= (/ y 5) x) (and (< x (/ y 3)) (>= (/ y 10) x))))