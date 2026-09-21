import CORALean.ContSet.ConZonotope.Real.Operations.RowBound

/-!
# `ConZonotope.tightenCoeff`

[1, Alg. 1], lines 3-5: row `i`'s bound on coefficient `j`, met with the running box `E`
— a no-op where the row does not mention `j`. `rowBound` is line 4's `Rⱼ ← (12)`; the
`Rⱼ ← Rⱼ ∩ (12)` then `Eⱼ ← Eⱼ ∩ Rⱼ` of the paper's own lines 4-5 collapses to the one
intersection here, since `Eⱼ` only ever narrows by meeting `Rⱼ` and both start at
`[-1,1]`, so `Eⱼ` stays `Rⱼ` clipped to `[-1,1]` throughout.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-5: row `i`'s bound on coefficient `j`, met with the running box. -/
noncomputable def ConZonotope.tightenCoeff {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng) (E : Interval (Vec ℝ ng)) : Interval (Vec ℝ ng) :=
  if A i j = 0 then E else                                                   -- 3. if a_ij ≠ 0
    let R := ConZonotope.rowBound A b i j E                                  -- 4. Rj ← (12)
    { inf := Function.update E.inf j (max (E.inf j) (min R.1 R.2))
      sup := Function.update E.sup j (min (E.sup j) (max R.1 R.2)) }         -- 5. Ej ← Ej ∩ Rj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
