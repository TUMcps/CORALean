# targets

Executable code, one directory per language. Each holds the sources in `src/`
and a `README.md` recording how that code came to be.

```
targets/
  c/     Lean's own compiler output, copied verbatim  (generated)
  cpp/   written by hand against the Lean sources     (transcribed)
```

The theorems live in `lean/`. What differs between these directories is only how
much of that guarantee survives the trip.

## Where the guarantee goes

The float layer is written entirely against `FloatOps F`; `SoundFloatArithmetic`,
`toReal`, ℝ, and every `Proofs/` file are erased at compile time. That fragment —
around 800 lines — is the whole export surface, and it is parametric in `F`, so
the C++ mirror of `FloatOps` is a traits struct and the algorithms are templates
over it.

Four ways to get from there to running code, in increasing order of what they
cost and what they guarantee:

**A — link Lean's generated C.** No transcription, so it *is* the verified
function. But every `F` is a boxed `lean_object*`, `Vec F n` is a closure, and
linking needs the Lean runtime and GMP. Realized in [`c/`](c/), not as a product
but as the reference to test against.

**B — write the C++ by hand, Lean as specification.** Fast and idiomatic. The
theorems become documentation of what the C++ must satisfy, tied to reality by
differential testing against A rather than by proof. Realized in [`cpp/`](cpp/);
this is what we run today, and its weakness is exactly that the tie is testing
rather than proof.

**C — generate the C++ from the Lean definitions.** The computable fragment is
first-order and small: structure literals, `fun i => …` over `Fin`, one `if`,
structural recursion in `sumUp`/`dotDown`, `Fin.append`, and `Split`. A `MetaM`
pass emitting templates over that is a few hundred lines, not a compiler. It
removes transcription risk, which is B's only real weakness — the generated code
is then the code the theorems are about, modulo the printer and the C++ compiler.
The reason B is written as templates over a `FloatOps` traits struct is so that C
has a fixed target to emit rather than a design problem to solve.

**D — deep embedding with a verified printer.** Define an imperative IR in Lean,
prove the algorithms against it, verify the IR → C++ printer. The only option
where "the C++ is verified" is literally true, and several times the work of
everything built so far. Not planned; recorded so the ceiling is known.

## What none of them close

The theorems are about a `FloatOps F` instance. Instantiating `F` at binary64 is
an assumption about the toolchain, not a proof, and it is sharp:

- `-ffast-math`, FMA contraction, and x87 excess precision each independently
  break the `FloatOps` axioms — they must be off, and pinned in the build
- **no overflow or underflow.** `Dyadic` has an unbounded exponent, which is
  exactly this assumption, and is why it needed no axioms. binary64 has both
  ends: `toReal_half` fails on subnormals, and `add_le_addUp` fails at overflow
  if it saturates the wrong way. Carried as a written assumption for now, not a
  side condition in the types.

Rounding mode is set once and never changed: the downward operations are derived
from the upward ones through `neg`, so a run never calls `fesetround` in its
inner loop.
