module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Uminus
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# CORA's `minus` with a vector minuend, at any scalar

`-S + p`, as `ContSet.minusFrom`, the point a vector of the representation's own scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `minus` for a numeric minuend `p`: `S = -S + p`. -/
def ContSet.minusFromScalar (p : Vec 𝕋 n) (s : S n) : S n :=
  Plus.plus (ContSet.uminus (𝕋 := 𝕋) s) (OfScalarPoint.ofVec (𝕋 := 𝕋) p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
