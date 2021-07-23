
(assert 
(forall ( (x1 Int) (x2 Int))
	(exists ((y Int))(
and (
< (+ (+ (* 4 x1) (div x2 2)) 1 ) (* 3 y)
) (
> (+ (+ (div x1 4) (div x2 2)) 3 ) (* 4 y)
)
))))
