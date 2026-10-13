module

public import CORALean.ContSet.Zonotope.Real.Operations.VolumeRatio
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `volumeRatio` of an over-approximation is at least one

If `P` contains `Z`, every window's projection of `P` contains that of `Z` (a projection is a
linear image), so the measure ratio is at least one, and so is its `1/d`-th power and the mean.
The zonotope's projections are compact, hence of finite measure, and must have positive measure
(a degenerate window divides by zero where CORA answers `Inf`).

Source: [1].

## References

* [1] `contSet/@zonotope/volumeRatio.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {d k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.one_le_volumeRatio (Z : Zonotope (Vec ℝ (d + k))) (P : HPolytope (Vec ℝ (d + k)))
    (hd : 0 < d) (hZP : Z.construct ⊆ P.construct)
    (hpos : ∀ i : Fin (k + 1), 0 < MeasureTheory.volume
      (Z.project (fun j : Fin d => (⟨j + i, by omega⟩ : Fin (d + k)))).construct) :
    1 ≤ Z.volumeRatio P := by -- --- PROOF ---
  unfold Zonotope.volumeRatio
  simp only
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  calc ((k + 1 : ℕ) : ENNReal) = ∑ _i : Fin (k + 1), (1 : ENNReal) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => ?_
  set proj : Fin d → Fin (d + k) := fun j => ⟨j + i, by omega⟩ with hproj
  have hsub : (Z.project proj).construct ⊆
      (LinearMap.funLeft ℝ ℝ proj) '' P.construct := by
    rw [Zonotope.project, ← Zonotope.map_exact]
    exact Set.image_mono hZP
  have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  have hfin : MeasureTheory.volume (Z.project proj).construct < ⊤ :=
    (Zonotope.isCompact_construct _).measure_lt_top
  refine ENNReal.one_le_rpow ?_ (by positivity)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (hpos i).ne') (Or.inl hfin.ne), one_mul]
  exact hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
