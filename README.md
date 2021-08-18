# tethys

Tethys is a toy functional programming language based on a System Fω-based core calculus. This language is mostly for learning about type systems, but I am going to make it into something half-fleshed (as opposed to fully-fleshed). It's not going to be *efficient* (most likely), but it will be a good learning experience.

There are two parts of Tethys: the surface language, and the core calculus. The core calculus is the intermediate representation of Tethys which is used for type checking and inference, and for interpretation. The surface language is the higher-level interface that is eventually desugared by the compiler/interpreter to the core calculus.

The reference implementation in Rust will probably not use any particular "tricks" in terms of interpretation (VM, JIT, AOT compilation to native, etc.), instead just using a simple tree-walk interpreter or similar.

This language was created in order to conduct informal research (i.e., not actually discovering anything interesting, probably) on type systems, especially bidirectional typechecking and polymorphism. Tethys is named as such as it is the name of the co-orbital moon to Calypso; as my work on this language is "co-orbital", so to speak, to my work on Calypso.

More information on Calypso (the language, of course) is available at [https://calypso-lang.github.io](https://calypso-lang.github.io).

## "Paper"

The source for the "paper" (really just a typeset informal writeup) is in [`paper.tex`][paper.tex] (requires pdftex). At some points there may be a PDF in the repository but there is no guarantee that it is up-to-date with the LaTeX source.
