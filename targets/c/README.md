# c — Lean's own C output

`src/` is the C that Lean's compiler emits for `lean/`, copied verbatim. It is
generated, not written: edits here are lost on the next export. It is checked in
because `lean/.lake/` is git-ignored.

## Regenerating

```bash
./export-from-lake.sh              # clean rebuild, then copy (several minutes)
./export-from-lake.sh --no-build   # copy what is in .lake right now
```

Lean never deletes the C of a renamed module, so an incremental build tree
accumulates dead files — at one point 36 of 90, including a `ContSetWithError`
long since gone. Hence the clean, scoped to `CORALean` because a bare
`lake clean` also wipes Mathlib's 6.3 GB build. The file list comes from the
`.lean` sources, so a module missing its C fails the export.

`PROVENANCE.txt` records toolchain, source commit, and file count per export.

## What it is for

This is the reference implementation: what the theorems say about
`Zonotope.mtimes` they say about *this* code, since it is the compiler's own
translation rather than a transcription. So it is the oracle for
[`../cpp`](../cpp), and the tie-breaker when hand-written C++ and Lean disagree.

## What it is not

Not a numerics library: every `F` is a boxed, refcounted `lean_object*`, and
`Vec F n` is a closure — `radius` on an `n × h` matrix does `n · h` closure
applications. Linking needs the Lean runtime and GMP. That cost is why
[`../cpp`](../cpp) is written by hand.

## Layout

Mirrors the Lean modules: `src/CORALean/Float/ContSet/Zonotope/API.c`
comes from the `.lean` file at the same path. Proof modules are included despite
compiling to nothing — theorems are erased, but each module still emits the
initializer the link needs.

## Toolchain

Pinned by `lean/lean-toolchain`; other versions are not expected to produce
matching output. Compile with that toolchain's bundled `leanc`, which supplies
the runtime headers:

```bash
"$(cd ../../lean && lean --print-prefix)/bin/leanc" -c src/CORALean/…/API.c
```

Note that `lean --print-prefix` must be run from `lean/` — the repository root
has no `lean-toolchain`, so elan answers with the global default instead.
