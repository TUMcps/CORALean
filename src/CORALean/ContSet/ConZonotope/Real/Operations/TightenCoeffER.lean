import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeff
import Mathlib.Data.EReal.Basic

/-!
# `ConZonotope.tightenCoeffER`

[1, Alg. 1 (R)], [2, Alg. 1], lines 3-5 with both outputs: row `i`'s bound on coefficient `j`
met with the running `R_j` (line 4) and with the running `E_j` (line 5).

The state is the pair `(E, R)`. `E` is an `Interval (Vec ℝ n_g)`, as `tightenCoeff` keeps it.
`R` starts at `[-∞, +∞]` and so is a pair of endpoint vectors in `EReal`, lower first.
Line 5's `E_j ← E_j ∩ R_j` is `tightenCoeff`'s `E_j` met with line 4's bound: `E_j` already
lies inside every earlier bound on `R_j`, so meeting it with the accumulated `R_j` or with
the newest bound alone gives the same interval.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-5 on the state `(E, R)`, `R` as its lower and upper endpoint vectors. -/
noncomputable def ConZonotope.tightenCoeffER {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng)
    (S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))) :
    Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal)) :=
  if A i j = 0 then S else                                                   -- 3. if a_ij ≠ 0
    let Rij := ConZonotope.rowBound A b i j S.1                              -- a_ij⁻¹ b_i − Σ ...
    let R : (Fin ng → EReal) × (Fin ng → EReal) :=
      (Function.update S.2.1 j (max (S.2.1 j) ((min Rij.1 Rij.2 : ℝ) : EReal)),
       Function.update S.2.2 j (min (S.2.2 j) ((max Rij.1 Rij.2 : ℝ) : EReal)))  -- 4. Rj ← Rj ∩ ...
    let E := ConZonotope.tightenCoeff A b i j S.1                            -- 5. Ej ← Ej ∩ Rj
    (E, R)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
