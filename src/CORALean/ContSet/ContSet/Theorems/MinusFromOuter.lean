module

public import CORALean.ContSet.ContSet.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.UminusOuter
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# `minusFrom` encloses the reflected translate
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `p - x` with `x` in `S` is in `minusFrom p S`: `uminus_outer`, then `plus_outer`. -/
theorem ContSet.minusFrom_outer (p : Vec ℝ n) (s : S n) :
    (fun x => p - x) '' construct s ⊆ construct (ContSet.minusFrom (𝕋 := 𝕋) p s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Plus.plus_outer _ _ ⟨-x, ContSet.uminus_outer s ⟨x, hx, rfl⟩, p,
    OfPoint.mem_ofPoint _, (sub_eq_neg_add p x).symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
