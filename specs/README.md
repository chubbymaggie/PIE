# Specifications for OCaml modules

## Notes
- The synthesized features have input variables names as `x0g`, `x1g` and so on ...


## BatAvlTree

#### BatAvlTree.check (t)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: true
postcondition: (res = true)
```

#### BatAvlTree.is_empty (t)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (height(t) = 0)
postcondition: (res = true)
```

#### BatAvlTree.singleton_tree (v)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: true
postcondition: (height(res) > 0)

precondition: false
postcondition: (height(res) = 0)
```

#### BatAvlTree.create (l,v,r)

```
precondition: ((x0g > (x2g + 1)) || (x2g > (x0g + 1)))
postcondition: exception thrown

precondition: (!(x0g > (x2g + 1)) && !(x2g > (x0g + 1)))
postcondition: terminates normally

precondition: true
postcondition: (height(res) > 0)

precondition: false
postcondition: (height(res) = 0)
```

#### BatAvlTree.make_tree (l,v,r)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: true
postcondition: (height(res) > 0)

precondition: false
postcondition: (height(res) = 0)
```

#### BatAvlTree.left_branch (t)

```
precondition: (height(t) = 0)
postcondition: exception thrown

precondition: !((height(t) = 0))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (height(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (height(res) = 0)

precondition: false
postcondition: (t = res)

precondition: true
postcondition: (height(t) > height(res))

precondition: false
postcondition: (height(t) = height(res))
```

#### BatAvlTree.right_branch (t)

```
precondition: (height(t) = 0)
postcondition: exception thrown

precondition: !((height(t) = 0))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (height(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (height(res) = 0)

precondition: false
postcondition: (t = res)

precondition: true
postcondition: (height(t) > height(res))

precondition: false
postcondition: (height(t) = height(res))
```

#### BatAvlTree.split_leftmost (t)

```
precondition: (height(t) = 0)
postcondition: exception thrown

precondition: !((height(t) = 0))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (height(l) > 0)

precondition: ~~ FAILED ~~
postcondition: (height(l) = 0)
```

#### BatAvlTree.split_rightmost (t)

```
precondition: (height(t) = 0)
postcondition: exception thrown

precondition: !((height(t) = 0))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (height(r) > 0)

precondition: ~~ FAILED ~~
postcondition: (height(r) = 0)
```

#### BatAvlTree.root (t)

```
precondition: (height(t) = 0)
postcondition: exception thrown

precondition: !((height(t) = 0))
postcondition: terminates normally
```

#### BatAvlTree.concat (l,r)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (!(height(r) = 0) || !(height(l) = height(r)))
postcondition: (height(res) > 0)

precondition: (height(r) = 0) && (l = r)
postcondition: (height(res) = 0)
```



## String

#### String.get (s,i)

```
precondition: ((i < 0) || !((#len(s) > i)))
postcondition: exception thrown

precondition: !((i < 0)) && (#len(s) > i)
postcondition: terminates normally
```

#### String.set (s, i, c)

```
precondition: ((i < 0) || !((#len(s) > i)))
postcondition: exception thrown

precondition: !((i < 0)) && (#len(s) > i)
postcondition: terminates normally

precondition: true
postcondition: (#len(res) > 0)

precondition: false
postcondition: (#len(res) = 0)
```

#### String.create (i)

```
precondition: (i < 0)
postcondition: exception thrown

precondition: !((i < 0))
postcondition: terminates normally

precondition: !((i = 0))
postcondition: (#len(res) > 0)

precondition: (i = 0)
postcondition: (#len(res) = 0)

precondition: false
postcondition: (i > #len(res))

precondition: true
postcondition: (i = #len(res))
```

#### String.make (i, c)

```
precondition: (i < 0)
postcondition: exception thrown

precondition: !((i < 0))
postcondition: terminates normally

precondition: !((i = 0))
postcondition: (#len(res) > 0)

precondition: (i = 0)
postcondition: (#len(res) = 0)
```

#### String.copy (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: true
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.sub (s,i1,i2)

```
precondition: ((i1 < 0) || (i2 < 0) || (x2g > ((#len(x0g)) - x1g)))
postcondition: exception thrown

precondition: !((i1 < 0)) && !((i2 < 0)) && (x2g <= ((#len(x0g)) - x1g))
postcondition: terminates normally

precondition: !((i2 = 0))
postcondition: (#len(res) > 0)

precondition: (i2 = 0)
postcondition: (#len(res) = 0)
```

#### String.fill (s0, i0, i1, c)

```
precondition: ((i0 < 0) || (i1 < 0) || (x2g > ((#len(x0g)) - x1g)))
postcondition: exception thrown

precondition: !((i0 < 0)) && !((i1 < 0)) && (x2g <= ((#len(x0g)) - x1g))
postcondition: terminates normally

precondition: !((#len(s0) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s0) = 0)
postcondition: (#len(res) = 0)
```

#### String.blit (s0, i0, s1, i1, il)

```
precondition: exception thrown
postcondition: O O M

precondition: terminates normally
postcondition: O O M

precondition: !((#len(s0) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s0) = 0)
postcondition: (#len(res) = 0)
```

#### String.concat (s, sl)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (#les(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (#len(res) = 0)
```

#### String.trim (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: true
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.escape (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: true
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.index (s, c)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res > 0)

precondition: ~~ FAILED ~~
postcondition: (res = 0)
```

#### String.rindex (s, c)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res > 0)

precondition: ~~ FAILED ~~
postcondition: (res = 0)
```

#### String.index_from (s, i, c)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res > 0)

precondition: ~~ FAILED ~~
postcondition: (res = 0)
```

#### String.rindex_from (s, i, c)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res > 0)

precondition: ~~ FAILED ~~
postcondition: (res = 0)
```

#### String.contains (s, c)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res = true)
```

#### String.contains_from (s, i, c)

```
precondition: ((i < 0) || (#len(s) < i))
postcondition: exception thrown

precondition: !((i < 0)) && !((#len(s) < i))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res = true)
```

#### String.rcontains_from (s, i, c)

```
precondition: ((i < 0) || !((#len(s) > i)))
postcondition: exception thrown

precondition: !((i < 0)) && (#len(s) > i)
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res = true)
```

#### String.uppercase (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: (#len(s) = 0)
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.lowercase (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: (#len(s) = 0)
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.capitalize (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: (#len(s) = 0)
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.uncapitalize (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !((#len(s) = 0))
postcondition: (#len(res) > 0)

precondition: (#len(s) = 0)
postcondition: (#len(res) = 0)

precondition: (#len(s) = 0)
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: true
postcondition: (#len(s) = #len(res))
```

#### String.compare (s0, s1)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res > 0)

precondition: (#eql(s0, s1))
postcondition: (res = 0)
```



## List

#### List.length (l)

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

#### List.hd (l)

```
precondition: len(l) = 0
postcondition: exception thrown

precondition: !(len(l) = 0)
postcondition: terminates normally
```

#### List.tl (l)

```
precondition: len(l) = 0
postcondition: exception thrown

precondition: !(len(l) = 0)
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (len(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (len(res) = 0)

precondition: false
postcondition: l = res

precondition: true
postcondition: len(l) > len(res)

precondition: false
postcondition: len(l) = len(res)
```

#### List.nth (l, n)

```
precondition: (n < 0 || !(len(l) > n))
postcondition: exception thrown

precondition: len(l) > n && !(n < 0)
postcondition: terminates normally
```

#### List.rev (a)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: !(len(a) = 0)
postcondition: len(res) > 0

precondition: len(a) = 0
postcondition: len(res) = 0

precondition: (x0g = (rev x0g))
postcondition: a = res

precondition: false
postcondition: len(a) > len(res)

precondition: true
postcondition: len(a) = len(res)
```

#### List.append (l0, l1)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (!((len(l1) = 0)) || !((len(l0) = len(l1))))
postcondition: len(res) > 0

precondition: len(l1) = 0 && len(l0) = len(l1)
postcondition: len(res) = 0
```

#### List.rev_append (l0, l1)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (!((len(l1) = 0)) || !((len(l0) = len(l1))))
postcondition: (len(res) > 0)

precondition: (len(l1) = 0) && (l0 = l1)
postcondition: (len(res) = 0)
```

#### List.concat (l)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: len(res) > 0

precondition: ~~ FAILED ~~
postcondition: len(res) = 0

precondition: ~~ FAILED ~~
postcondition: len(l) > len(res)

precondition: ~~ FAILED ~~
postcondition: len(l) = len(res)
```

#### List.flatten (l)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: len(res) > 0

precondition: ~~ FAILED ~~
postcondition: len(res) = 0

precondition: ~~ FAILED ~~
postcondition: len(l) > len(res)

precondition: ~~ FAILED ~~
postcondition: len(l) = len(res)
```

#### List.mem (m, l)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: res = true
```

#### List.assoc (a, l)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally
```

#### List.mem_assoc (a, l)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res = true)
```

#### List.remove_assoc (a, l)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (len(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (len(res) = 0)
```

#### List.split (l)

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

#### List.combine (l0, l1)

```
precondition: !(len(l0) = len(l1))
postcondition: exception thrown

precondition: len(l0) = len(l1)
postcondition: terminates normally

precondition: !(len(l1) = 0)
postcondition: len(res) > 0

precondition: len(l1) = 0
postcondition: len(res) = 0
```
