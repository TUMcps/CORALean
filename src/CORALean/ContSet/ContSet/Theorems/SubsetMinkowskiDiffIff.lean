module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The Galois connection behind the Minkowski difference

`X ⊆ minkowskiDiff S T` and `X + T ⊆ S` say the same thing, which makes `minkowskiDiff S T` the
*largest* set that `T` can be added to without leaving `S` — the reason a `MinkDiff` implementation
may only under-approximate it.

Here rather than beside the definition in `ContSet.lean`, which holds the interface; a fact about
one of its definitions is a theorem, and `Theorems/` is where a theorem goes. Nothing mentions a
representation, so it is stated on bare sets. No hypotheses: it is `Set.mem_add` unfolded.

## Inputs
* `X` – set
* `S` – minuend
* `T` – subtrahend

## Hypotheses
* none

## Conclusion
* `X` lies in `S ⊖ T` iff `X + T` lies in `S`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Adding `T` and taking the Minkowski difference by `T` are adjoint: `X` fits
inside `minkowskiDiff S T` exactly when `X + T` fits inside `S`. -/
theorem subset_minkowskiDiff_iff (X S T : Set α) :
    X ⊆ minkowskiDiff S T ↔ X + T ⊆ S := by -- --- PROOF ---
  constructor
  · -- a point of `X` already answers for every `y ∈ T` by definition
    intro hX z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    exact hX hx y hy
  · -- conversely, `x + y` is a point of `X + T`
    intro hX x hx y hy
    exact hX (Set.add_mem_add hx hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
