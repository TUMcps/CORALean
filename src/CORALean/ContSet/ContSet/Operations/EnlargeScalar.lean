import CORALean.ContSet.ContSet.Operations.MinusScalar
import CORALean.ContSet.ContSet.Operations.Times

/-!
# CORA's `enlarge` at any scalar

`S - c`, scaled by the factors, then `+ c` back, with `c` the set's centre as a vector of the
representation's scalar (`ScalarCentre`), so a float representation runs it.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [OfScalarPoint 𝕋 S] [ScalarCentre 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enlarge`: `c = center(S); S = S - c; S = S .* factor; S = S + c`. -/
def ContSet.enlargeScalar (s : S n) (factor : Vec 𝕋 n) : S n :=
  let c := ScalarCentre.centreVec s
  let shifted := ContSet.minusScalar s c
  let scaled := ContSet.times factor shifted
  Plus.plus scaled (OfScalarPoint.ofVec (𝕋 := 𝕋) c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
