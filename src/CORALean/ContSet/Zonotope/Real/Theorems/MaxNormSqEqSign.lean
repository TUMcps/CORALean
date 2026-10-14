module

public import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormSumEqGram
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeExact
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The maximum zonotope norm as a sign-vector program

[1, Prop. 1], with [1, Eq. 14]: `⌈Z⌉² = -min_{u ∈ {-1, 1}ᵐ} uᵀ M u + λ m` with `M = λ I - GᵀG`,
and `M ≽ 0` for `λ` the largest eigenvalue of `GᵀG`. The maximum over the box is taken at a sign
vector — a convex function on the zonotope's vertex hull peaks at a vertex — and on a sign
vector `uᵀ u = m` turns `uᵀ GᵀG u` into `-uᵀ M u + λ m` for every `λ`. `M ≽ 0` needs exactly
that `λ` bounds the Rayleigh quotient of `GᵀG`, which the largest eigenvalue is the least number
to do.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `‖·‖₂²` is convex. -/
theorem aux_convexOn_sq_norm₂ :
    ConvexOn ℝ Set.univ (fun x : Vec ℝ n => ‖x‖₂ ^ 2) := by -- --- PROOF ---
  have hc : ConvexOn ℝ Set.univ (fun x : Vec ℝ n => ‖toEuclidean x‖) := by
    have := (convexOn_norm (convex_univ (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)))).comp_linearMap
      (toEuclidean (n := n)).toLinearEquiv.toLinearMap
    simpa [Function.comp_def] using this
  have hp := hc.pow (fun x _ => norm_nonneg _) 2
  refine hp.congr fun x _ => ?_
  simp only [Pi.pow_apply]
  rw [norm_toEuclidean]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.maxNormSq_eq_sign (Z : Zonotope (Vec ℝ n)) (lam : ℝ) :
    Z.maxNormSq = -(Finset.univ.inf' Finset.univ_nonempty fun s : Fin Z.h → Bool =>
        (fun j => if s j then (1 : ℝ) else -1) ⬝ᵥ
          ((lam • (1 : Mat ℝ Z.h Z.h) - Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) *ᵥ
            fun j => if s j then (1 : ℝ) else -1)) + lam * Z.h ∧
      ((∀ u : Vec ℝ Z.h, u ⬝ᵥ ((Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) *ᵥ u) ≤ lam * (u ⬝ᵥ u)) →
        (lam • (1 : Mat ℝ Z.h Z.h) -
          Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k).PosSemidef) := by -- --- PROOF ---
  set Gram : Mat ℝ Z.h Z.h := Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k with hGram
  set M : Mat ℝ Z.h Z.h := lam • (1 : Mat ℝ Z.h Z.h) - Gram with hM
  set σ : (Fin Z.h → Bool) → Vec ℝ Z.h := fun s j => if s j then (1 : ℝ) else -1 with hσ
  -- on a sign vector `uᵀ u = m`, so the Gram form is `-uᵀ M u + λ m`
  have hsign : ∀ s, ‖∑ j, σ s j • Z.G j‖₂ ^ 2 = -(σ s ⬝ᵥ (M *ᵥ σ s)) + lam * Z.h := by
    intro s
    have hss : σ s ⬝ᵥ σ s = Z.h := by
      simp only [dotProduct, hσ]
      rw [Finset.sum_congr rfl fun j _ => show (if s j then (1 : ℝ) else -1) *
        (if s j then (1 : ℝ) else -1) = 1 by split_ifs <;> norm_num]
      simp
    rw [Z.sq_norm₂_sum_eq_gram, hM, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, hss, smul_eq_mul]
    ring
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    fun s => σ s ⬝ᵥ (M *ᵥ σ s)
  refine ⟨?_, fun hlam => ?_⟩
  -- the value is the greatest, so the supremum
  · refine IsGreatest.csSup_eq ⟨⟨σ s₀, fun j => by simp only [hσ]; split_ifs <;> norm_num,
      by rw [hsign, hs₀]⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    -- `∑ βⱼ gⱼ` lies in the hull of the sign combinations, where the convex `‖·‖₂²` peaks
    have hmem : ∑ j, β j • Z.G j ∈ convexHull ℝ (Set.range fun s => ∑ j, σ s j • Z.G j) := by
      have hZ0 : ∑ j, β j • Z.G j ∈ (⟨Z.h, 0, Z.G⟩ : Zonotope (Vec ℝ n)).construct :=
        ⟨β, hβ, by rw [zero_add]⟩
      rw [← Zonotope.vPolytope_exact, VPolytope.construct_eq_convexHull] at hZ0
      refine convexHull_mono ?_ hZ0
      rintro _ ⟨l, rfl⟩
      exact ⟨signEquiv Z.h l, by simp [Zonotope.vPolytope, Zonotope.corner, hσ]⟩
    obtain ⟨_, ⟨s, rfl⟩, hle⟩ := aux_convexOn_sq_norm₂.exists_ge_of_mem_convexHull
      (Set.subset_univ _) hmem
    refine le_trans hle ?_
    rw [hsign]
    have := Finset.inf'_le (fun s => σ s ⬝ᵥ (M *ᵥ σ s)) (Finset.mem_univ s)
    linarith
  -- `M ≽ 0` when `λ` bounds the Rayleigh quotient
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp [hM, hGram, Matrix.one_apply, dotProduct_comm, eq_comm]
    · rw [star_trivial, hM, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      linarith [hlam x]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
