module

public import CORALean.ContSet.Ellipsoid.Real.Definitions.IsApproxLownerJohn
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# A sandwich of ellipsoids gives an approximate Löwner-John ellipse

[1, Eq. 5]: if the ellipsoid `E(E_j, s)` contains the set `P` and `E(E_j/(n²(1+ε)), s)`
is contained in it, then `E* = E_j/(1+ε)` is an `ε`-approximate Löwner-John ellipse of `P`, since
`E*/n² = E_j/(n²(1+ε))` and `(1+ε) E* = E_j`. It is how Goffin's test (5) ends the iteration.

## Inputs
* `ε` – approximation tolerance
* `C` – set
* `E` – ellipsoid

## Hypotheses
* `hε` – `-1 < ε`
* `hin` – the scaled inner ellipsoid lies in `C`
* `hout` – `C` lies in `E`

## Conclusion
* `E/(1+ε)` is an `ε`-approximate Löwner-John ellipse of `C`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5]: the sandwich puts `E_j/(1+ε)` among the `ε`-approximate Löwner-John ellipses. -/
theorem Ellipsoid.isApproxLownerJohn_of_sandwich {ε : ℝ} (hε : -1 < ε) (C : Set (Vec ℝ n))
    (E : Ellipsoid n)
    (hin : (Ellipsoid.ofShape ((1 / ((n : ℝ) ^ 2 * (1 + ε))) • E.Q) E.q).construct ⊆ C)
    (hout : C ⊆ E.construct) : -- --- CONCL ---
    Ellipsoid.IsApproxLownerJohn ε C (Ellipsoid.ofShape ((1 / (1 + ε)) • E.Q) E.q)
    := by -- --- PROOF ---
  have hε' : 0 < 1 + ε := by linarith
  have hpsd : ((1 / (1 + ε)) • E.Q).PosSemidef := E.psd.smul (by positivity)
  unfold Ellipsoid.IsApproxLownerJohn
  rw [Ellipsoid.ofShape_eq hpsd]
  refine ⟨?_, ?_⟩
  · -- the inner shape is `E_j/(n²(1+ε))`
    have : (1 / (n : ℝ) ^ 2) • (1 / (1 + ε)) • E.Q = (1 / ((n : ℝ) ^ 2 * (1 + ε))) • E.Q := by
      rw [smul_smul, one_div_mul_one_div]
    simpa only [this] using hin
  · -- and the outer one is `E_j` again
    have : (1 + ε) • (1 / (1 + ε)) • E.Q = E.Q := by
      rw [smul_smul, mul_one_div_cancel hε'.ne', one_smul]
    rw [this, Ellipsoid.ofShape_eq E.psd]
    exact hout

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
