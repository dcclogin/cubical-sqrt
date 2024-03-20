
Modified from [chessai](https://github.com/chessai/theseus).

- fixed some pretty-prints
- remove the REPL
- [To be done] fix the module system
- [To be done] rewriting rules of the language? 

# Running Theseus Programs

No REPL. We use the ghci REPL to run it:

```shell
$ cd src/
$ ghci Theseus.hs
GHCi, version X.X.X: https://www.haskell.org/ghc/  :? for help
[1 of 8] Compiling Theseus.AbstractSyntax ( Theseus\AbstractSyntax.hs, interpreted )
[2 of 8] Compiling Theseus.Debug    ( Theseus\Debug.hs, interpreted )
[3 of 8] Compiling Theseus.Coverage ( Theseus\Coverage.hs, interpreted )
[4 of 8] Compiling Theseus.Pretty   ( Theseus\Pretty.hs, interpreted )
[5 of 8] Compiling Theseus.Parse    ( Theseus\Parse.hs, interpreted )
[6 of 8] Compiling Theseus.Semantics ( Theseus\Semantics.hs, interpreted )
[7 of 8] Compiling Theseus.Eval     ( Theseus\Eval.hs, interpreted )
[8 of 8] Compiling Theseus          ( Theseus.hs, interpreted )
Ok, 8 modules loaded.
ghci> run "sqrt.ths"
Typechecking...
Evaluating...
[...]
ghci> 
```

The module system is not properly working currently. Require all `.ths` files to be under `src/` to work.

