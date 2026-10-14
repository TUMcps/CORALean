module

public import CORALean.ContSet.Ellipsoid.Real.Definitions.IsApproxLownerJohn
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
`E*/n² = E_j/(n²(1+ε))` and `(1+ε) E* = E_j`. In generators `G` of `E_j`: the inner ellipsoid
has the generator `G/(n√(1+ε))`, and `E*` has `G/√(1+ε)`, which `IsApproxLownerJohn` scales
by `1/n` and by `√(1+ε)`. It is how Goffin's test (5) ends the iteration.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5]: the sandwich puts `E_j/(1+ε)` among the `ε`-approximate Löwner-John ellipses. -/
theorem Ellipsoid.isApproxLownerJohn_of_sandwich {ε : ℝ} (hε : -1 < ε) (C : Set (Vec ℝ n))
    (E : Ellipsoid n)
    (hin : (⟨E.k, E.c, (1 / ((n : ℝ) * Real.sqrt (1 + ε))) • E.G⟩ : Ellipsoid n).construct ⊆ C)
    (hout : C ⊆ E.construct) :
    Ellipsoid.IsApproxLownerJohn ε C
      ⟨E.k, E.c, (1 / Real.sqrt (1 + ε)) • E.G⟩ := by -- --- PROOF ---
  have hs : Real.sqrt (1 + ε) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  refine ⟨?_, ?_⟩
  · -- the inner generator is `(1/n) (1/√(1+ε)) G`
    simpa only [smul_smul, one_div, mul_inv] using hin
  · -- and the outer one is `G` again
    have : Real.sqrt (1 + ε) • (1 / Real.sqrt (1 + ε)) • E.G = E.G := by
      rw [smul_smul, mul_one_div_cancel hs, one_smul]
    simpa only [this] using hout

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
