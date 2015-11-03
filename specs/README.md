# Specifications for OCaml modules

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
precondition: ((height(r) > (height(l) + 1)) | (height(l) > (height(r) + 1)))
postcondition: exception thrown

precondition: ((height(l) <= (height(r) + 1)) & (height(r) <= (height(l) + 1)))
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
precondition: empty(t)
postcondition: exception thrown

precondition: (! empty(t))
postcondition: terminates normally

precondition: (! empty(left(t)))
postcondition: (height(res) > 0)

precondition: empty(left(t))
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
precondition: empty(t)
postcondition: exception thrown

precondition: (! empty(t))
postcondition: terminates normally

precondition: (! empty(right(t)))
postcondition: (height(res) > 0)

precondition: empty(right(t))
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
precondition: empty(t)
postcondition: exception thrown

precondition: (! empty(t))
postcondition: terminates normally

precondition: (height(t) > 1)
postcondition: (height(l) > 0)

precondition: (1 = height(t))
postcondition: (height(l) = 0)
```

#### BatAvlTree.split_rightmost (t)

```
precondition: empty(t)
postcondition: exception thrown

precondition: (! empty(t))
postcondition: terminates normally

precondition: (height(t) > 1)
postcondition: (height(r) > 0)

precondition: (1 = height(t))
postcondition: (height(r) = 0)
```

#### BatAvlTree.root (t)

```
precondition: empty(t)
postcondition: exception thrown

precondition: (! empty(t))
postcondition: terminates normally
```

#### BatAvlTree.concat (l,r)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (! (empty(r) & empty(l)))
postcondition: (height(res) > 0)

precondition: (empty(r) & empty(l))
postcondition: (height(res) = 0)
```



## String

#### String.get (s,i)

```
precondition: ((0 > i) | ((#len(s)) <= i))
postcondition: exception thrown

precondition: ((0 <= i) & ((#len(s)) > i))
postcondition: terminates normally
```

#### String.set (s, i, c)

```
precondition: (((0 > i) | (0 = (#len(s)))) || ((#len(s)) <= i))
postcondition: exception thrown

precondition: ((0 <= i) & ((#len(s)) > i))
postcondition: terminates normally

precondition: true
postcondition: (#len(res) > 0)

precondition: false
postcondition: (#len(res) = 0)
```

#### String.create (i)

```
precondition: (0 > i)
postcondition: exception thrown

precondition: (0 <= i)
postcondition: terminates normally

precondition: (i > 0)
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
precondition: (0 > i)
postcondition: exception thrown

precondition: (0 <= i)
postcondition: terminates normally

precondition: (i > 0)
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

precondition: (((#len(s)) > 1) || (1 = (#len(s))))
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
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
precondition: (((0 > i1) | (0 > i2)) || (i2 > ((#len(s)) - i1)))
postcondition: exception thrown

precondition: ((0 <= i2) & (0 <= i1)) && (i2 <= ((#len(s)) - i1))
postcondition: terminates normally

precondition: ((i2 > 0) & (0 <= i1))
postcondition: (#len(res) > 0)

precondition: (i2 = 0)
postcondition: (#len(res) = 0)
```

#### String.fill (s0, i0, i1, c)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (#len(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (#len(res) = 0)
```

#### String.blit (s0, i0, s1, i1, il)

```
precondition: ~~ FAILED ~~
postcondition: exception thrown

precondition: ~~ FAILED ~~
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (#len(res) > 0)

precondition: ~~ FAILED ~~
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

precondition: ~~ FAILED ~~
postcondition: (#len(res) > 0)

precondition: ~~ FAILED ~~
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
postcondition: (#eql(s, res))

precondition: ~~ FAILED ~~
postcondition: (#len(s) > #len(res))

precondition: ~~ FAILED ~~
postcondition: (#len(s) = #len(res))
```

#### String.escape (s)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (((#len(s)) > 1) || (1 = (#len(s))))
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
postcondition: (#eql(s, res))

precondition: false
postcondition: (#len(s) > #len(res))

precondition: ~~ FAILED ~~
postcondition: (#len(s) = #len(res))
```

#### String.index (s, c)

```
precondition: (! (contains(s, c)))
postcondition: exception thrown

precondition: (contains(s, c))
postcondition: terminates normally

precondition: (! (contains((#get(s, 0)), c)))
postcondition: (res > 0)

precondition: (contains((#get(s, 0)), c))
postcondition: (res = 0)
```

#### String.rindex (s, c)

```
precondition: (! (contains(s, c)))
postcondition: exception thrown

precondition: (contains(s, c))
postcondition: terminates normally

precondition: (contains((#sub(s, 1, ((#len(s)) - 1))), c))
postcondition: (res > 0)

precondition: (! (contains((#sub(s, 1, ((#len(s)) - 1))), c)))
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

precondition: contains(s,c)
postcondition: (res = true)
```

#### String.contains_from (s, i, c)

```
precondition: ((i > (#len(s))) || (0 > i))
postcondition: exception thrown

precondition: (((0 <= i) & ((#len(s)) > i)) || (i = (#len(s))))
postcondition: terminates normally

precondition: ~~ FAILED ~~
postcondition: (res = true)
```

#### String.rcontains_from (s, i, c)

```
precondition: (((#len(s)) <= i) || (0 > i))
postcondition: exception thrown

precondition: (((0 <= i) & ((#len(s)) > 1)) || (0 = i)) && ((#len(s)) > i)
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

precondition: ((#len(s)) > 0)
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
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

precondition: ((#len(s)) > 0)
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
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

precondition: (((#len(s)) > 1) || (1 = (#len(s))))
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
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

precondition: (((#len(s)) > 1) || (1 = (#len(s))))
postcondition: (#len(res) > 0)

precondition: (0 = (#len(s)))
postcondition: (#len(res) = 0)

precondition: ~~ FAILED ~~
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

precondition: (! empty(l))
postcondition: (res > 0)

precondition: empty(l)
postcondition: (res = 0)

precondition: false
postcondition: len(l) > res

precondition: true
postcondition: len(l) = res
```

#### List.hd (l)

```
precondition: empty(l)
postcondition: exception thrown

precondition: (! empty(l))
postcondition: terminates normally
```

#### List.tl (l)

```
precondition: empty(l)
postcondition: exception thrown

precondition: (! empty(l))
postcondition: terminates normally

precondition: (len(l) > 1)
postcondition: (len(res) > 0)

precondition: (1 = len(l))
postcondition: (len(res) = 0)

precondition: false
postcondition: (l = res)

precondition: true
postcondition: (len(l) > len(res))

precondition: false
postcondition: (len(l) = len(res))
```

#### List.nth (l, n)

```
precondition: (((0 > n) | (n > len(l))) || (n = len(l)))
postcondition: exception thrown

precondition: ((0 <= n) & (len(l) > n))
postcondition: terminates normally
```

#### List.rev (a)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: (! empty(l))
postcondition: (len(res) > 0)

precondition: empty(l)
postcondition: (len(res) = 0)

precondition: (l = rev(l))
postcondition: (l = res)

precondition: false
postcondition: (len(l) > len(res))

precondition: true
postcondition: (len(l) = len(res))
```

#### List.append (l0, l1)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ((! empty(l0)) || (! empty(l1)))
postcondition: (len(res) > 0)

precondition: empty(l0) && empty(l1)
postcondition: (len(res) = 0)
```

#### List.rev_append (l0, l1)

```
precondition: false
postcondition: exception thrown

precondition: true
postcondition: terminates normally

precondition: ((! empty(l1)) || (! empty(l0)))
postcondition: (len(res) > 0)

precondition: empty(l1) && empty(l0)
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

precondition: (m in l)
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

precondition: (! empty(l))
postcondition: (len(r0) > 0)

precondition: empty(l)
postcondition: (len(r0) = 0)

precondition: (! empty(l))
postcondition: (len(r1) > 0)

precondition: empty(l)
postcondition: (len(r1) = 0)

precondition: false
postcondition: len(r0) > len(r1)

precondition: true
postcondition: len(r0) = len(r1)
```

#### List.combine (l0, l1)

```
precondition: (! (len(l0) = len(l1)))
postcondition: exception thrown

precondition: (len(l0) = len(l1))
postcondition: terminates normally

precondition: (! empty(l0))
postcondition: (len(res) > 0)

precondition: empty(l1)
postcondition: (len(res) = 0)
```
