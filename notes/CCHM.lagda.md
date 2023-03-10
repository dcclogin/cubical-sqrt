```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
```


## Syntax of the core language


### Syntax of `ð` elements

```text
r, s := 0 | 1 | i | 1 â r | r â§ s | r â¨ s
```


### Syntax of terms and types

```text
t,u,A,B := x | Î»x : A. t | t u | (x : A) â B       Î -types
        | (t, u) | t.1 | t.2 | (x : A) Ã B          Î£-types
        | 0 | s u | natrec t u | â                  Natural numbers
        | <i> t | t r | Path A t u                  Path types
        | [Ïâ tâ, Ïâ tâ, ..., Ïâ tâ]                Systems
        | compâ± A [Ï â¦ u] aâ                       Compositions
```

### Syntax of contexts

```text
Î, Î := ()
     | Î, x : A
     | Î, i : ð
     | Î, Ï              Restrictions
```

### Syntax of face formula

```text
Ï, Ï := 0ð½ | 1ð½
     | (i = 0)
     | (i = 1)
     | Ï â§ Ï
     | Ï â¨ Ï
```

Some operations can be defined with `comp` in the language:

- `transp`
- `fill`


## Composition

If `Î, Ï â¢ u : A`, then `Î â¢ a : A[Ï â¦ u]` means `Î â¢ a : A` **AND** `Î, Ï â¢ a = u : A`.

It can be read as "in the restricted context `Ï`, `a` agrees with `u`".
In other words, `a` is a evidence that `u` (defined on `Ï`) is *extensible*.

Composition says extensibility of partial elements is preserved along paths.

```text
Î â¢ Ï : ð½
Î, (i : ð) â¢ A
Î, Ï, (i : ð) â¢ u : A
Î â¢ aâ : A(i0) [Ï â¦ u(i0)]
---------------------------------------------
Î â¢ compâ± A [Ï â¦ u] aâ : A(i1) [Ï â¦ u(i1)]
```

Here `u` is a **partial path**, while `u(i0)` and `u(i1)` are **partial elements**.

It can be easily translated into Cubical Agda code:

```agda
postulate
  comp' : â {â}
        â (A : â i â Type â)
        â (Ï : I)
        â (u : â i â Partial Ï (A i))
        â A i0 [ Ï â¦ u i0 ]
        -------------------------
        â A i1 [ Ï â¦ u i1 ]
```

### Two special cases

1. When `Ï = 1ð½`, `u(i1)` becomes a "total element" (no context restrictions):
```text
Î â¢ compâ± A [1ð½ â¦ u] aâ = u(i1) : A(i1)
```

2. When `Ï = 0ð½`, composition corresponds to transport:
```text
Î â¢ transpâ± A a = compâ± A [] a : A(i1)
```

In Cubical Agda, `transp` is primitive. Can we define our own `transp` with `comp`?


### Kan filling operation


```text
Î, i : ð â¢ fillâ± A [Ï â¦ u] aâ = compÊ² A(i/iâ§j) [Ï â¦ u(i/iâ§j), (i=0) â¦ aâ] aâ : A
```
Let

```text
Î, i : ð â¢ v = fillâ± A [Ï â¦ u] aâ : A
```

`v` satisfies:

1. when `i=0`, it's just identity function.
```text
Î â¢ v(i0) = aâ : A
```

2. when `i=1`, it's the "full composition".
```text
Î â¢ v(i1) = compâ± A [Ï â¦ u] aâ : A(i1)
```


```agda
fill' : â {â}
      â (A : â i â Type â)
      â (Ï : I)
      â (u : â i â Partial Ï (A i))
      â A i0 [ Ï â¦ u i0 ]
      -------------------------------
      â (i : I) â A i
fill' A Ï u aâ i = outS (comp' A* (Ï â¨ ~ i) u* (inS (outS aâ)))
  where
    A* : _
    A* = Î» j â A (i â§ j)

    u* : â j â Partial (Ï â¨ ~ i) _
    u* j (Ï = i1) = u (i â§ j) 1=1
    u* j (i = i0) = outS aâ

```
