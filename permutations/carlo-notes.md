## Square roots of permutations

Recall that every permutation can be written as a product of disjoint cycles,
and these commute; thus the square root of a permutation can be obtained as the
product of the square roots of its disjoint cycles. A permutation is square iff
for each even number $2n$, there is an even number of $2n$-length cycles in its
disjoint cycle decomposition.

Thus every permutation $f : X\to X$ can be made squarable by embedding it in
$f + f : (X+X)\to (X+X)$, analogously to how a classical computation can be made
quantum by adding an imaginary part to each bit. For instance, the permutation
$(-1\ 1)$ is not square, but
$$ (-1\ 1)(-i\ i) = (1\ i\ (-1)\ (-i))^2 $$
in much the same way that the $X$ gate is not classically square but has a
rotation as its quantum square root.

More conservatively, we can embed every permutation into a square permutation by
adding one more $2n$-length cycle for each $n$ for which there is an odd number
of $2n$-length cycles. Is there an analogous notion of a "conservative" addition
of qubits to a classical algorithm to achieve speedup?

Based on the above observations, consider the following plan:
- Start with a first-order lambda calculus over finite types
  ($0$,$1$,$+$,$\times$).
- Use Amr's _Information Effects_ paper to embed this language in reversible
  functions over finite types.
- Further embed this in _square_ reversible functions over finite types by
  duplicating the necessary bits.

Why might we want to take square roots of functions? Possible ideas include SIMD
settings where one wishes to "slow down" an operation which is used half as
often as other operations in order to avoid buffering.
