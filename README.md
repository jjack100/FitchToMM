# FitchToMM
FitchToMM is a tool for converting Fitch-style proofs (for first-order logic) to the [Metamath](https://us.metamath.org/) format, and provides a Metamath database formalizing natural deduction for these proofs to use.
A longer-term goal for this project is for it to serve as a backend to a UI that can provide a prettier visual editor for proofs; see also [fol-parser](https://github.com/jjack100/fol-parser) for transforming formulae written in $\LaTeX$ into the S-expression syntax used here.

## What is Metamath?
Metamath is a file format (and associated [program](https://github.com/metamath/metamath-exe)) for storing mathematical proofs in a way that can be very efficiently verified by a computer.
Metamath itself is not tied to any one specific formal system or set of axioms.
Instead, it enables the specification of arbitrary formal systems to build collections (or "databases") of theorems proved within them.

The largest such database is [set.mm](https://github.com/metamath/set.mm).
Set.mm is fundamentally a Hilbert-style system (although [clever techniques](https://us.metamath.org/mpeuni/mmnatded.html) have been developed for emulating natural deduction style reasoning within it).
By contrast, the system used here uses natural deduction from the start (for an example of another approach somewhat similar to ours, see also Frédéric Liné's [nat.mm](https://web.archive.org/web/20120402081711/http://wiki.planetmath.org/cgi-bin/wiki.pl/Natural_deduction_based_metamath_system)).

## What is a Fitch-style proof?
Fitch notation is one way of presenting proofs in natural deduction.
It is characterized by:
  1. Allowing a hierarchical structure of nested "subproofs" used to track temporary assumptions made "for the sake of argument".
  2. Arranging steps in a line-by-line format, so that each step can cite a previous step or subproof by line number.

Typically this is depicted in a visual diagram that uses indented sections to indicate the scope of each subproof.

## How to use
This repository is a Nix flake that provides:
  1. A Haskell library, and
  2. An executable providing a simple command-line interface to it, which can read a JSON representation of a list of Fitch-style proofs and generate Metamath output.

If you have Nix installed, you can build the project by running `nix build`.
The resulting executable will be under `./result/bin/fitch2mm`.

### Running fitch2mm
`fitch2mm` can be passed a JSON file to be read (see the `examples` directory for what format is expected).
Basic usage is:
```
fitch2mm <input-file> --output <output-file>
```
For example, to read the theorems from the `examples` directory:
```
./result/bin/fitch2mm ./examples/theorems.json --output example.mm
```
This will generate the output `example.mm` in the current directory.
If any mistakes are encountered, it will emit warnings but still try to generate the rest of the proof, inserting `?`s in place of the problematic steps.
(It is also possible that the proof will be fully completed despite the presence of mistakes, if the steps with mistakes ultimately go unused.)

### Verifying generated proofs
The Nix flake also provides a development shell that includes the [metamath program](https://github.com/metamath/metamath-exe) and [mmj2](https://github.com/digama0/mmj2), which can be used to verify the generated proofs.

> [!TIP]
> It is recommended to use [direnv](https://github.com/direnv/direnv) (and its [VS Code extension](https://github.com/direnv/direnv-vscode) if using VS Code) to automatically enter the shell when opening the project.
Otherwise you can enter the development shell with `nix develop`.

For example, to verify the `example.mm` file we generated, you can run:
```
metamath "READ example.mm" "VERIFY PROOF *"
```

You can also run `cabal test` to run the test suite.

## Acknowledgements
- Thank you to Marnix Klooster for creating [Hmm](https://github.com/spl/hmm), a Metamath verifier written in Haskell; it is being used here as part of the test suite for automatically verifying the correctness of outputs.

---

Copyright © 2026  Joseph Jackson

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

See the [LICENSE](LICENSE) file for details.