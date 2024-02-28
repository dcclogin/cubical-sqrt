## Example1: Nat2

```
Nat2 := Bool * Bool
Nat3 := Bool * Bool * Bool
Nat4 := Bool * Bool * Bool * Bool

-- consider a very special variant of square root (call it "naively non-classical")
sqrt2 :: f:(A <-> A) -> (A * Bool <-> A * Bool)

add1 :: Nat2 <-> Nat2 :: sub1
| (a, 0) <-> (a, 1)
| (0, 1) <-> (1, 0)
| (1, 1) <-> (0, 0)

sqrt2(add1) :: Nat2 * Bool <-> Nat2 * Bool :: sqrt2(sub1)
| (a, 0, 0) <-> (a, 0, 1)   -- pattern to be merged
| (a, 0, 1) <-> (a, 1, 0)
| (0, 1, 0) <-> (0, 1, 1)   -- pattern to be merged
| (0, 1, 1) <-> (1, 0, 0)
| (1, 1, 0) <-> (1, 1, 1)   -- pattern to be merged
| (1, 1, 1) <-> (0, 0, 0)


-- here we need an algorithm to "merge" patterns (!)
-- we see that [sqrt(add1::Nat2 <-> Nat2)] is indeed [add1::Nat3 <-> Nat3]
-- inductively [sqrt(add1::Nat3 <-> Nat3)] equals to [add1::Nat4 <-> Nat4]
-- ...

add1 :: Nat3 <-> Nat3 :: sub1
| (b, a, 0) <-> (b, a, 1)
| (a, 0, 1) <-> (a, 1, 0)
| (0, 1, 1) <-> (1, 0, 0)
| (1, 1, 1) <-> (0, 0, 0)


-- we need a map to "drop" the last bit
dropLastBit :: f:(A * Bool <-> A * Bool) -> (A <-> A)

-- f == dropLastBit(sqrt2(f) . sqrt2(f))
```


## Example2: Recursive Nat

```
data Nat where
    Z :: Nat
    S :: Nat -> Nat


add1 :: Nat <-> Nat :: sub1
| x            <-> ret $ inr x
| lab $ Z      <-> ret $ inl () 
| lab $ S n    <-> lab $ n
| ret $ inl () <-> Z
| ret $ inr n  <-> S n

where ret :: 1 + Nat
      lab :: Nat

-- evaluation sequence 
-- S S S Z -> ret $ inr (S S S Z) -> S S S S Z




-- for types like [unfoldNat::Nat <-> Nat + 1::foldNat], sqrt2 won't work. need a way to get around?

-- [f : A <-> B]         -> [A * B <-> A * B]
-- [f : Nat <-> Nat + 1] -> [Nat * (Nat + 1) <-> Nat * (Nat + 1)]

unfoldNat :: Nat <-> Nat + 1 :: foldNat
| Z   <-> inr ()
| S n <-> inl n


unfoldNat^ :: Nat * (Nat + 1) <-> Nat * (Nat + 1) :: foldNat^
| (Z,   inr ())  <-> (Z, inr ())
| (S n, inr ())  <-> (Z, inl n)
| (Z,   inl n)   <-> (S n, inr ())
| (S n, inl n)   <-> (S n, inl n)


sqrt2(unfoldNat^) :: Nat * (Nat + 1) * Bool <-> Nat * (Nat + 1) * Bool :: sqrt2(foldNat^)
| (Z,   inr (), 0)  <-> (Z, inr (), 1)
| (Z,   inr (), 1)  <-> (Z, inr (), 0)

| (S n, inr (), 0)  <-> (Z, inl n, 1)
| (Z,   inl n, 1)   <-> (Z, inl n, 0)     -- interesting pattern for Z -> inr ()

| (Z,   inl n, 0)   <-> (S n, inr (), 1)  -- interesting pattern for Z -> inr ()
| (S n, inr (), 1)  <-> (S n, inr (), 0)

| (S n, inl n, 0)   <-> (S n, inl n, 1)
| (S n, inl n, 1)   <-> (S n, inl n, 0)
```