The prototype formula for a quantum state:

$$ g \cdot \begin{bmatrix} x \\ 
                           y \cdot e^{\frac{i\pi \cdot r}{2}} 
           \end{bmatrix} $$

where $` g `$ represents global phases, and $` r `$ represents relative (local) phases.

In Theseus, the type `(1 + 1) * Bool * Four * Eight` represents a quantum state. The following is the translation from instances of the formula into the typed values:

- $` g \cdot \begin{bmatrix} 1 \\ 
                             0 \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inL, FF, _, _`
- $` g \cdot \begin{bmatrix} 1 \\ 
                             -i \cdot e^{\frac{i\pi \cdot r}{2}} 
             \end{bmatrix} `$ into `inL, TT, _, _`


