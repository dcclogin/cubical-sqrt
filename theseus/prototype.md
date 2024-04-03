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


