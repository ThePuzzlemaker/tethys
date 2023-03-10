# Tethys

[![CI Status][ci_badge]][ci_link] [![License][license_badge]][license_link] [![Discord](https://img.shields.io/discord/822290196057948171?style=flat-square&color=blue)](https://discord.gg/26X6ChQQcG) ![Lines of Code][tokei_loc]

[tokei_loc]: https://img.shields.io/tokei/lines/github/ThePuzzlemaker/Tethys?style=flat-square

[ci_badge]: https://img.shields.io/github/actions/workflow/status/ThePuzzlemaker/tethys/ci.yml?branch=main&style=flat-square
[ci_link]: https://github.com/ThePuzzlemaker/Tethys/actions

[license_badge]: https://img.shields.io/badge/license-MIT%2FApache--2.0-blue?style=flat-square
[license_link]: #license

[calypso]: https://calypso-lang.github.io/

Tethys is a toy functional programming language based on a System F-based core calculus. 

This language is mostly for learning about type systems, but I am going to make it into something half-fleshed (as opposed to fully-fleshed). It's not going to be *efficient* (most likely), but it will be a good learning experience.

Note that this code is very work-in-progress. Contributions are welcome (and encouraged!), but it's likely that as a toy langauge, this will never be in a state that is helpful or efficient to use in production. If you want a language that will (eventually) be robust (enough), see [Calypso][calypso].

## Example

The following example is an implementation of [FizzBuzz](https://en.wikipedia.org/wiki/Fizz_buzz) up to 100. This is also available at [`support/examples/fizzbuzz.tys`](./support/examples/fizzbuzz.tys). Note that this is currently pseudocode, though it will likely not change much by the time most features are implemented.

```elixir
def main
  : () -> ()
  = \_.
    each (fizzbuzz 100) println

def fizzbuzz
  : Int -> List[String]
  = \max.
    map (rangeI 1 100) (\n.
      if (divides n 15)
      then "FizzBuzz"
      else if (divides n 3)
      then "Fizz"
      else if (divides n 5)
      then "Buzz"
      # Typeclasses soon(tm)
      else intToString n)
```

## Internals and Motivation

There are two parts of Tethys: the surface language, and the core calculus. The core calculus is the intermediate representation of Tethys which is used for type checking and inference, and for interpretation. The surface language is the higher-level interface that is eventually desugared by the compiler/interpreter to the core calculus.

The reference implementation in Rust will probably not use any particular "tricks" in terms of interpretation (VM, JIT, AOT compilation to native, etc.), instead just using a simple tree-walk interpreter or similar. (At some point, it may end up compiling to Calypso's SaturnVM.)

This language was created in order to conduct informal research (i.e., not actually discovering anything interesting, probably) on type systems, especially bidirectional typechecking and polymorphism. Tethys is named as such as it is the name of the co-orbital moon to Calypso; as my work on this language is "co-orbital", so to speak, to my work on Calypso.

More information on Calypso (the language, of course) is available at [https://calypso-lang.github.io][calypso].

This implementation is partially based on an implementation of bidirectional typechecking with unification of higher-rank polymorphism created by [Mark Barbone (aka MBones/mb64)](https://github.com/mb64). A slightly modified version of this implementation is available at [`support/tychk_nbe.ml`](./support/tychk_nbe.ml). The original is available [in this Gist](https://gist.github.com/mb64/f49ccb1bbf2349c8026d8ccf29bd158e#file-tychk_nbe-ml).

A list of resources and bibliography used to make this is available in the [paper](#paper).

### "Paper"

The source for the "paper" (really just a typeset informal writeup) is in [`paper/paper.tex`](paper/paper.tex) (requires pdftex). At some points there may be a PDF in the repository but there is no guarantee that it is up-to-date with the LaTeX source.

## Contribution

I have yet to draft up a CONTRIBUTING.md. If you'd like to contribute and don't know where to start, feel free to open an issue, ping me on Discord or contact me elsewhere. I'll let you know if there's anything I think you can help with, and if so give you some pointers. Contributions are greatly appreciated!

There is a semi-functional VSCode extension / TextMate grammar in [`support/highlight`](./support/highlight). It's not perfect, but it works well enough.

### Repository Overview

- `paper/`: Source and occasionally PDF for the "paper" (really just a typeset informal writeup). See [this section](#paper) for a bit more information.
- `support/`: Support files, including grammars, examples, tests, etc. See [its README](./support/README.md) for a bit more information.
- `src/`: The glorious source code.
  - `bin/uitest/`: UI testing. WIP
  - `bin/tethys.rs`: The main binary.
  - `ast/`: AST definition. Name resolution data is stored elsewhere.
  - `resolve/`: Name resolution.
  - `parse/`: Lexing and parsing.

Many modules have doc comments, but some do not. However, much of the code is (usually) self-explanatory, and when not I try to add comments and doc comments. If you have trouble understanding something and are wondering what something does, let me know, and I'll try to explain it to you.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
