;x1 + x2 < y /\ (x1 < 7 \/ x2 + 9 = y) /\ (y < x1 + 4 \/ x2 > x1 - 5 * y)
(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (< (+ x1 x2) y) (and (or (< x1 7) (= (+ x2 9) y)) (or (< y (+ x1 4)) (> x2 (- x1 (* 5 y)))))))