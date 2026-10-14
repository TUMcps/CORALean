module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# An ellipsoid as a zonotope

Through the box, as everything reaching a zonotope does here: a tighter
zonotope enclosure of an ellipsoid is a fitting problem — how many generators,
pointed which way — rather than a conversion, and CORA leaves that choice to the
caller too.

The box step is tight and the box-to-zonotope step is exact, so all the loss is
in the first, and it is the loss of an axis-aligned enclosure of a rotated set.

CORA's `'inner:norm'` and `'outer:norm'` are [1, Thm. 2] and [1, Thm. 4]: points `S` on the unit
sphere, ideally spread evenly ([1, Lemma 4]), scaled by the inverse of a bound on the maximum,
or below the minimum, norm of `Z(S, 0)` and mapped by the ellipsoid's generator.
`zonotopeInnerNorm` and `zonotopeNorm` take `S` and the bound; the guarantees hold for any `S`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}

noncomputable def Ellipsoid.zonotope (E : Ellipsoid n) : Zonotope (Vec ℝ n) :=
  E.interval.zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonotope_contains (E : Ellipsoid n) : E.construct ⊆ E.zonotope.construct :=
  subset_trans E.interval_contains (Interval.zonotope_contains _)

/-- [1, Thm. 2]: `Z(r^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeInnerNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    (r : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.c
  G := fun j => (√r)⁻¹ • (E.G *ᵥ S j)

/-- [1, Thm. 2]: `r ≥ ⌈Z(S, 0)⌉²` puts the scaled zonotope in the ellipsoid. -/
theorem Ellipsoid.contains_zonotopeInnerNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    {r : ℝ} (hr : 0 < r) (hS : (⟨m, 0, S⟩ : Zonotope (Vec ℝ E.k)).maxNormSq ≤ r) :
    (E.zonotopeInnerNorm S r).construct ⊆ E.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  change ∀ j : Fin m, |β j| ≤ 1 at hβ
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  -- the coefficient point `u = r^{-1/2} ∑ βⱼ sⱼ` is in the unit ball
  have hle := le_trans (Zonotope.sq_norm₂_le_maxNormSq ⟨m, 0, S⟩ hβ) hS
  refine ⟨(√r)⁻¹ • ∑ j, β j • S j, ?_, ?_⟩
  · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs, mul_one]
    calc ‖∑ j, β j • S j‖₂ = √(‖∑ j, β j • S j‖₂ ^ 2) := (Real.sqrt_sq (norm₂_nonneg _)).symm
      _ ≤ √r := Real.sqrt_le_sqrt hle
  · show E.c + ∑ j, β j • ((√r)⁻¹ • (E.G *ᵥ S j)) = E.c + E.G *ᵥ ((√r)⁻¹ • ∑ j, β j • S j)
    rw [Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum]
    simp only [Matrix.mulVec_smul, smul_comm (√r)⁻¹]

/-- [1, Thm. 4]: `Z(l^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    (l : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.c
  G := fun j => (√l)⁻¹ • (E.G *ᵥ S j)

/-- [1, Thm. 4]: a ball of radius `√l` inside `Z(S, 0)` — `l ≤ ⌊Z(S, 0)⌋²` — makes the scaled
zonotope enclose the ellipsoid. -/
theorem Ellipsoid.zonotopeNorm_contains (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    {l : ℝ} (hl : 0 < l)
    (hball : ∀ u : Vec ℝ E.k, ‖u‖₂ ≤ √l → u ∈ (⟨m, 0, S⟩ : Zonotope (Vec ℝ E.k)).construct) :
    E.construct ⊆ (E.zonotopeNorm S l).construct := by -- --- PROOF ---
  rintro _ ⟨u, hu, rfl⟩
  have hs : 0 < √l := Real.sqrt_pos.mpr hl
  -- `√l u` is a combination of the points, so `u` is one of the scaled points
  obtain ⟨β, hβ, heq⟩ := hball (√l • u) (by
    rw [norm₂_smul, abs_of_pos hs]
    exact mul_le_of_le_one_right hs.le hu)
  rw [zero_add] at heq
  change ∀ j : Fin m, |β j| ≤ 1 at hβ
  refine ⟨(β : Fin m → ℝ), hβ, ?_⟩
  show E.c + E.G *ᵥ u = E.c + ∑ j, β j • ((√l)⁻¹ • (E.G *ᵥ S j))
  have hu' : u = (√l)⁻¹ • ∑ j, β j • S j := by
    rw [← heq, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hu', Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum]
  simp only [Matrix.mulVec_smul, smul_comm (√l)⁻¹]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
