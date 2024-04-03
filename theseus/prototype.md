The prototype formula for a quantum state:

$$ g \cdot \begin{bmatrix} x \\ 
                           y \cdot e^{\frac{i\pi \cdot r}{2}} 
           \end{bmatrix} $$

where $` g `$ represents global phases, and $` r `$ represents relative (local) phases.

In Theseus, the type `(1 + 1) * Bool * Four * Eight` represents a prototype quantum state. In this type, `(1 + 1) * Bool` are input/output type for `sqrt`; `Four` corresponds to the relative phase $` r `$; `Eight` corresponds to the global phase $` g `$. The following is the translation from instances of the formula into the typed values:

- $` g \cdot \begin{bmatrix} 1 \\ 
                             0 \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inL (), FF, _, _`
- $` g \cdot \begin{bmatrix} 1 \\ 
                             -i \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inL (), TT, _, _`
- $` g \cdot \begin{bmatrix} 0 \\ 
                             1 \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inR (), FF, _, _`
- $` g \cdot \begin{bmatrix} 1 \\ 
                             i \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inR (), TT, _, _`


Taking into consideration of symmetries, clearly there are some equations that should hold, e.g.
$` g \cdot \begin{bmatrix} 1 \\ 
                           -i \cdot e^{\frac{i\pi \cdot 1}{2}} 
           \end{bmatrix} `$
shoud be equal to
$` g \cdot \begin{bmatrix} 1 \\ 
                           i \cdot e^{\frac{i\pi \cdot 3}{2}} 
           \end{bmatrix} `$ :

`inL (), TT, C1, _` = `inR (), TT, C3, _`




Take $` V = \begin{bmatrix} \frac{1+i}{2} && \frac{1-i}{2} \\ \frac{1-i}{2} && \frac{1+i}{2} \end{bmatrix} `$ for example:

$$ V\ket{0} = \frac{1+i}{2} \cdot \begin{bmatrix} 1 \\ 
                                                  -i 
                                  \end{bmatrix} $$

$$ V\ket{1} = \frac{1-i}{2} \cdot \begin{bmatrix} 1 \\ 
                                                  i 
                                  \end{bmatrix} $$

Therefore `Eight` values for the global phases are:

$$ 1, \frac{1+i}{2}, i, \frac{-1+i}{2}, -1, \frac{-1-i}{2}, -i, \frac{1-i}{2} $$

In Thesues, we defined `next_8` and `prev_8` to go back-and-forth:

```haskell
iso next_8 : Eight = Eight
| E0 = E1 | E1 = E2 | E2 = E3 | E3 = E4 | E4 = E5 | E5 = E6 | E6 = E7 | E7 = E0

iso prev_8 : Eight = Eight
| next_8 a = a
```

## Problems

1. Four relative phases at `inL (), FF, _, _` map to the same prototype quantum state.
2. Need quite a lot translation maps to hold the equations from the symmetries of quantum states.
