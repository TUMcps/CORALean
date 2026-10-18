module

public import CORALean.ContSet.Zonotope.Real.Definitions.OverApproxIndex

@[expose] public section

/-!
# Ranking enclosures by volume ranks them by `Θ`

[1, Prop. 10]'s second claim: among enclosures of one zonotope, `Θ* = V(S_red)` is minimal
exactly where `Θ` is, so the cheaper index may be searched instead. Both sides divide by
the same `V(S_orig) > 0` and take the same `n`-th root, and `x ↦ (x / V)^{1/n}` is strictly
increasing on `[0, ∞)` — which is the printed proof, one step at a time.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10]: `Θ` orders two enclosures of `Sorig` as their volumes `Θ*` do. -/
theorem Zonotope.overApproxIndex_le_iff (hn : n ≠ 0) {Sorig : Zonotope (Vec ℝ n)}
    (hV : 0 < (MeasureTheory.volume Sorig.construct).toReal)
    (S₁ S₂ : Zonotope (Vec ℝ n)) : -- --- STMT ---
    S₁.overApproxIndex Sorig ≤ S₂.overApproxIndex Sorig
      ↔ (MeasureTheory.volume S₁.construct).toReal
        ≤ (MeasureTheory.volume S₂.construct).toReal := by -- --- PROOF ---
  simp only [Zonotope.overApproxIndex]
  have hexp : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  rw [Real.rpow_le_rpow_iff (div_nonneg ENNReal.toReal_nonneg hV.le)
    (div_nonneg ENNReal.toReal_nonneg hV.le) hexp, div_le_div_iff_of_pos_right hV]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
