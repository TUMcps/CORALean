module

public import CORALean.ContSet.ContSet.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.UminusOuter

@[expose] public section

/-!
# `minusFromScalar` encloses the reflected translate
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `p - x`, `x` in `S` and `p` read as reals, is in `minusFromScalar p S`: `uminus_outer`
then `plus_outer`. -/
theorem ContSet.minusFromScalar_outer (p : Vec 𝕋 n) (s : S n) :
    (fun x => toRealVec p - x) '' construct s ⊆ construct (ContSet.minusFromScalar p s) := by
  rintro _ ⟨x, hx, rfl⟩
  have h1 := ContSet.uminus_outer (𝕋 := 𝕋) s ⟨x, hx, rfl⟩
  exact Plus.plus_outer _ _ ⟨-x, h1, toRealVec p, OfScalarPoint.mem_ofVec _, neg_add_eq_sub _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
