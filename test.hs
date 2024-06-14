fun = \y -> let f = \x -> x in f y
idd = \x -> x
a = if True then fun else idd

b = if True then \y -> (let f = (\x -> x) in (f y, y)) else \x -> (x, True)

c = (a, b)