import CORALean.ContSet.Ellipsoid.Real.Operations.CutShape
import CORALean.Global.EuclideanNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One cut of Goffin's algorithm for zonotopes

[1, Sec. 4.6 (algorithm)], the iteration whose test failed: with `Φ : ξ ↦ E_j^{-1/2}ξ` mapping
`E(E_j, 0)` to the unit ball and the separator `a` of Sec. 4.5 for `Z′ = ΦZ`, cut the ball by
`(c := a/‖a‖, γ)`, `γ = 1/√(n(1+ε))`, which gives `E` of Lemma 4.3 (Eq. 16), and set
`E_{j+1} := Φ⁻¹(E)`: the image of `E(E, 0)` under `ξ ↦ E_j^{1/2}ξ`, of shape
`E_j^{1/2} E E_j^{1/2}`. The square root is the symmetric one, `CFC.sqrt`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped MatrixOrder

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.6 (algorithm)]: `E_{j+1} := Φ⁻¹(E)` for the cut `(a/‖a‖, 1/√(n(1+ε)))`. -/
noncomputable def Ellipsoid.goffinCut (ε : ℝ) (Ej : Mat ℝ n n) (a : Vec ℝ n) : Mat ℝ n n :=
  let Φinv := CFC.sqrt Ej
  let γ := 1 / Real.sqrt ((n : ℝ) * (1 + ε))
  let c := (‖a‖₂)⁻¹ • a
  let E := Ellipsoid.cutShape n c γ
  Φinv * E * Φinv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
