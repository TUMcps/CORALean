module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Minus
public import CORALean.ContSet.ContSet.Operations.Times

@[expose] public section

/-!
# CORA's `enlarge`: scaling about the center

`S - c`, scaled by the factors, then `+ c` back, with `c` the set's center.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enlarge`: `c = center(S); S = S - c; S = S .* factor; S = S + c`. -/
def ContSet.enlarge (s : S n) (factor : Vec 𝕋 n) : S n :=
  let c := Recenter.center s
  let shifted := ContSet.minus s c
  let scaled := ContSet.times factor shifted
  Plus.plus scaled (OfPoint.ofPoint c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
