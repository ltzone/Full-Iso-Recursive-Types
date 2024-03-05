# Full iso-recursive type system



### Exanple:

```
                                                          ------------------------------------- assump1
------------------------------------- assump1                (mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y)
------------------------------------- unfoldL             == (mu x. x -> x) -> (mu x. x -> x)
------------------------------------- unfoldL, unfoldR    ------------------------------------- unfoldR, unfoldL
(mu x. mu y. x -> y) = (mu x. x -> x)                     (mu y. (mu x. mu y. x -> y) -> y) == (mu x. x -> x)
----------------------------------------------------------------------------------------- arrfix (assump 1)
    (mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y)
==  (mu x. x -> x) -> (mu x. x -> x)
------------------------------------------------------------------------------------------ unfoldL
mu y. (mu x. mu y. x -> y) -> y =  (mu x. x -> x) -> (mu x. x -> x)
------------------------------------------------------------------------------------------ unfoldL, unfoldR
mu x. mu y. x -> y == mu x. x -> x
```

The resulting cast operator:
`unfold ; unfold; fix cx. ( ( unfold; unfold; cx ; fold )   -> (unfold; cx ; fold) ) ; fold `


### The Dual Exanple:

`
```
                                                          ------------------------------------- assump1
------------------------------------- assump1                (mu x. x -> x) -> (mu x. x -> x)
------------------------------------- unfoldR             == (mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y)
------------------------------------- unfoldL, unfoldR    ------------------------------------- unfoldL, unfoldR
(mu x. x -> x) == (mu x. mu y. x -> y)                    (mu x. x -> x) == (mu y. (mu x. mu y. x -> y) -> y)
----------------------------------------------------------------------------------------- arrfix (assump 1)
    (mu x. x -> x) -> (mu x. x -> x)
==  (mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y)
------------------------------------------------------------------------------------------ unfoldR
(mu x. x -> x) -> (mu x. x -> x) == mu y. (mu x. mu y. x -> y) -> y
------------------------------------------------------------------------------------------ unfoldL, unfoldR
mu x. x -> x == mu x. mu y. x -> y
```

`unfold; fix cx. ((unfold; cx; fold; fold) -> (unfold; cx; fold) ); fold; fold`

reverse cx = cx
reverse (c1 ; c2) = reverse c2 ; reverse c1


### TypCast is not symmetric example:

Assumption: `(mu x. x -> x) -> (mu x. x -> x) ==  (mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y)`
Goal : `(mu x. mu y. x -> y) == (mu x. x -> x)`


```
.... (the old proof)
--------------------------------------------- arrfix
(mu x. mu y. x -> y) -> (mu y. (mu x. mu y. x -> y) -> y) == (mu x. x -> x) -> (mu x. x -> x)
--------------------------------------------- unfoldL
mu y. (mu x. mu y. x -> y) -> y == (mu x. x -> x) -> (mu x. x -> x)
--------------------------------------------- unfoldL, unfoldR
(mu x. mu y. x -> y) == (mu x. x -> x)
```

