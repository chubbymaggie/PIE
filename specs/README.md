# Specifications for OCaml modules

## Notes
- The synthesized features have input variables names as `x0g`, `x1g` and so on ...

## List

### Properties

#### List.length

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !(len(l) = 0)
postcondition: res > 0

precondition: len(l) = 0
postcondition: res = 0

precondition: false
postcondition: len(l) > res

precondition: true
postcondition: len(l) = res
```

#### List.hd

```
precondition: len(l) = 0
postcondition: exception thrown

precondition: !(len(l) = 0)
postcondition: terminates normally

precondition: ((rev (tl x0g)) = (tl x0g)) && ((rev x0g) = x0g)
postcondition: for all le in l -> le = res

precondition: !(len(l) = 0)
postcondition: for any le in l -> le = res
```

#### List.nth

```
precondition: (!(n > 0) || !(len(l) > n)) && (!(n = 0) || len(l) = n)
postcondition: exception thrown

precondition: len(l) > n && (n > 0 || n = 0)
postcondition: terminates normally
```

#### List.mem

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: for any le in l -> m = le
postcondition: res = true
```

### Mutators

#### List.tl

```
precondition: len(l) = 0
postcondition: exception thrown

precondition: !(len(l) = 0)
postcondition: terminates normally

precondition: (! ((tl x0g) = []))
postcondition: len(res) > 0

precondition: !((! ((tl x0g) = []))) && ((rev (tl x0g)) = (tl x0g))
postcondition: len(res) = 0

precondition: false
postcondition: l = res

precondition: ((rev (tl x0g)) = (tl x0g)) && ((rev x0g) = x0g)
postcondition: for all le in l -> for all rese in res -> le = rese

precondition: (!(((rev (tl x0g)) = (tl x0g))) || ((hd (tl x0g)) = (hd x0g))) && (! ((tl x0g) = [])) && (((rev x0g) = x0g) || ((hd (tl x0g)) = (hd x0g)))
postcondition: for all le in l -> for any rese in res -> le = rese

precondition: ((rev (tl x0g)) = (tl x0g))
postcondition: for any le in l -> for all rese in res -> le = rese

precondition: (! ((tl x0g) = []))
postcondition: for any le in l -> for any rese in res -> le = rese

precondition: !(len(l) = 0)
postcondition: len(l) > len(res)

precondition: false
postcondition: len(l) = len(res)
```

#### List.append

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (!(l0 = l1) || for any l0e in l0 -> for any l1e in l1 -> l0e = l1e)
postcondition: len(res) > 0

precondition: len(l1) = 0 && len(l0) = len(l1)
postcondition: len(res) = 0

precondition: true
postcondition: len(res) = len(l0)+len(l1)

precondition: false
postcondition: len(res) != len(l0)+len(l1)
```

#### List.combine

```
precondition: !(len(l0) = len(l1))
postcondition: exception thrown

precondition: len(l0) = len(l1)
postcondition: terminates normally

precondition: len(l0) = len(l1) && !(len(l1) = 0)
postcondition: len(res) > 0

precondition: len(l0) = len(l1) && len(l1) = 0
postcondition: len(res) = 0
```

#### List.concat

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: for any le in l -> len(le) > 0
postcondition: len(res) > 0

precondition: !(for any le in l -> len(le) > 0)
postcondition: len(res) = 0

precondition: Failed
postcondition: len(l) > len(res)

precondition: Failed
postcondition: len(l) = len(res)

precondition: false
postcondition: len(res) > sum(len(l0:lN))

precondition: true
postcondition: len(res) = sum(len(l0:lN))

precondition: false
postcondition: len(res) < sum(len(l0:lN))
```

#### List.flatten

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: for any le in l -> len(le) > 0
postcondition: len(res) > 0

precondition: !(for any le in l -> len(le) > 0)
postcondition: len(res) = 0

precondition: Failed
postcondition: len(l) > len(res)

precondition: Failed
postcondition: len(l) = len(res)

precondition: false
postcondition: len(res) > sum(len(l0:lN))

precondition: true
postcondition: len(res) = sum(len(l0:lN))

precondition: false
postcondition: len(res) < sum(len(l0:lN))
```

#### List.rev

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !(len(a) = 0)
postcondition: len(res) > 0

precondition: len(a) = 0
postcondition: len(res) = 0

precondition: ((rev x0g) = x0g)
postcondition: a = res

precondition: ((rev x0g) = x0g) && (len(a) % 2 = 0 || ((rev (tl x0g)) = (tl x0g)))
postcondition: for all ae in a -> for all rese in res -> ae = rese

precondition: true
postcondition: for all ae in a -> for any rese in res -> ae = rese

precondition: ((rev (tl x0g)) = (tl x0g)) && ((rev x0g) = x0g)
postcondition: for any ae in a -> for all rese in res -> ae = rese

precondition: !(len(a) = 0)
postcondition: for any ae in a -> for any rese in res -> ae = rese

precondition: false
postcondition: len(a) > len(res)

precondition: true
postcondition: len(a) = len(res)
```

#### List.rev_append

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (!(l0 = l1) || for any l0e in l0 -> for any l1e in l1 -> l0e = l1e)
postcondition: len(res) > 0

precondition: len(l1) = 0 && len(l0) = len(l1)
postcondition: len(res) = 0

precondition: true
postcondition: len(res) = len(l0)+len(l1)

precondition: false
postcondition: len(res) != len(l0)+len(l1)
```

#### List.split

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !(len(l) = 0)
postcondition: len(r0) > 0

precondition: len(l) = 0
postcondition: len(r0) = 0

precondition: !(len(l) = 0)
postcondition: len(r1) > 0

precondition: len(l) = 0
postcondition: len(r1) = 0

precondition: false
postcondition: len(r0) > len(r1)

precondition: true
postcondition: len(r0) = len(r1)
```
