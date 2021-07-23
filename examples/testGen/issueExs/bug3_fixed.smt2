;(((((x1/3)+(x2/3))+4)<((-4)*y))&&(((x1/2)+3)<((-5)*y)))
(assert 
(forall ( (x1 Int) (x2 Int))
	(exists ((y Int))(
and (
	< (+ (div x1 2) 3) (* (- 5) y)
) (
	< (+ (+ (div x1 3) (div x2 3)) 4) (* (- 4) y)
)
))))
