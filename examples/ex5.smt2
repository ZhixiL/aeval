; pi = (y != x1 && y != x2)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun y () Int)

(assert (and (
    not(= y x1)
) (
    not(= y x2)
)))
(check-sat)