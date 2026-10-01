import CORALean.ContSet.ContSet.ContSet


import CORALean.ContSet.ContSet.Operations.Minus
import CORALean.ContSet.ContSet.Operations.Times

/-!
# CORA's `enlarge`: scaling about the centre

`S - c`, scaled by the factors, then `+ c` back, with `c` the set's centre.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recentre (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enlarge`: `c = center(S); S = S - c; S = S .* factor; S = S + c`. -/
def ContSet.enlarge (s : S n) (factor : Vec 𝕋 n) : S n :=
  let c := Recentre.centre s
  let shifted := ContSet.minus s c
  let scaled := ContSet.times factor shifted
  Plus.plus scaled (OfPoint.ofPoint c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
