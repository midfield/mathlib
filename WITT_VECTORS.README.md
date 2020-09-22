# Formalizing the Ring of Witt Vectors

## Installation instructions

### Installing Lean

The code is written and tested with the community fork of Lean 3, version 3.20.0.
To install it, please see: https://leanprover-community.github.io/get_started.html

We STRONGLY recommend following these directions, which will install elan,
the Lean version manager, which will choose the correct version of Lean automatically.
If you install a fixed version, make sure it is 3.20.0.

### Running the code from the Witt vector project

There are two ways to run the code of the Witt vector project.

1. Use the anonymized tar bundle provided with the paper.
   In this case, run `leanpkg build` in the root of the package to compile the code.
   We have included precompiled binaries in the tar.
   If your Lean installation is as expected (following the above directions),
   this command will check that the binaries match the source,
   which should take under 30 seconds.
   Otherwise, the compile may easily take 1~2 hours,
   and could possibly fail if you are using the wrong Lean version.

2. (Recommended) The anonymized code is also available as a branch of mathlib on github.
   See https://github.com/leanprover-community/mathlib/tree/witt-vectors-anon
   By following the installation instructions above,
   a tool called `leanproject` should have been installed.
   By running `leanproject get mathlib:witt-vectors-anon` this branch will automatically be cloned
   and precompiled binary artifacts will be downloaded from the cloud.

If you inspect the files in VSCode, you must use VSCode's `Open Folder` option
to open the project root directory.
You CANNOT open a single file (e.g. by double clicking on it) and browse interactively.
Easy way: from the command line, in the directory containing this file, type

    code .

and everything should work.

## Guide through the code

Our main contributions can be found in:

* `src/data/padics/ring_homs.lean`
* the contents of `src/ring_theory/witt_vector/`

Many other small contributions have already found their way into the main library,
and are harder to point at.

The file `witt_vector_preps.lean` inside `src/ring_theory/witt_vector/`
contains many preliminary results that should be distributed into other files in the library.

We will now explain how the other files correspond to the different subsections of the paper.

### Section 3

Section 3, and in particular Section 3.2 corresponds to the file `src/data/padics/ring_homs.lean`.
The material in 3.1 was added to `src/ring_theory/discrete_valuation_ring.lean` and
`src/data/padics/padic_integers.lean`, files that existed before this project began.
They are not anonymized but the authors and copyright holders are not necessarily the authors of
this paper.

### Section 4

* 4.1: `src/data/mv_polynomial/monad.lean`
* 4.2: `src/ring_theory/witt_vector/structure_polynomial.lean`,
       `src/ring_theory/witt_vector/witt_polynomial.lean`
* 4.3: `src/ring_theory/witt_vector/basic.lean` (the very top)
* 4.4: `src/ring_theory/witt_vector/is_poly.lean`
* 5.1: `src/ring_theory/witt_vector/basic.lean`
* 5.2: These tactics appear throughout, including in `basic.lean`.
       The `witt_simp` tactic appears in `is_poly.lean`.
       Tactic definitions are identified by the keyword `meta def`.
* 5.3: All in `src/ring_theory/witt_vector/`, `frobenius.lean`, `verschiebung.lean`, `mul_p.lean`,
       `teichmuller.lean`, `witt_sub.lean`, `identities.lean`.
* 5.4: `src/ring_theory/witt_vector/truncated.lean`, `src/ring_theory/witt_vector/compare.lean`

## Listing of the Witt vector directory:

basic.lean
compare.lean
frobenius.lean
identities.lean
init_tail.lean
is_poly.lean
mul_p.lean
structure_polynomial.lean
teichmuller.lean
truncated.lean
verschiebung.lean
witt_polynomial.lean
witt_sub.lean
witt_vector_preps.lean

## Import hierarchy:

witt_polynomial
|
structure_polynomial
|
basic
|
is_poly
|----------|-------------|------|----------|------------|
frobenius  verschiebung  mul_p  init_tail  teichmuller  witt_sub
|----------|-------------|      |
           identities           truncated
           |--------------------|
           compare