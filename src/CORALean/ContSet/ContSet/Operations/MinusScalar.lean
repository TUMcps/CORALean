module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# CORA's `minus` with a vector subtrahend, at any scalar

`S + (-p)` as `ContSet.minus` has it, the point now a vector of the representation's own scalar
and entering through `OfScalarPoint`, so a float representation runs it. Negation is exact in
every format, hence `NegScalar` and no rounding.
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

/-- CORA's `minus` for a numeric `p`: `S = S + (-p)`. -/
def ContSet.minusScalar (s : S n) (p : Vec 𝕋 n) : S n :=
  Plus.plus s (OfScalarPoint.ofVec (𝕋 := 𝕋) (-p))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
