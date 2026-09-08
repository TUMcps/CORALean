import CORALean.ContSet.ContSet.ContSet

/-!
# The Galois connection behind the Minkowski difference

`X ⊆ minkowskiDiff S T` and `X + T ⊆ S` say the same thing, which is what makes
`minkowskiDiff S T` the *largest* set that `T` can be added to without leaving
`S` — the reason a `MinkDiff` implementation may only under-approximate it.

Here rather than beside the definition in `ContSet.lean`, which holds the
interface and what it denotes; a fact proved about one of its definitions is a
theorem, and `Theorems/` is where a theorem goes. Nothing about it mentions a
representation, so it is stated on bare sets and every `construct` use below
is an instance of it.

No hypotheses at all: it is `Set.mem_add` unfolded against the definition, and
holds in any module.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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
