module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-!
# The `n`-th root of the box volume is concave

[1, Sec. IV-B, Step 3)]: `γ ↦ (∏ᵢ γ(i))^{1/n}` is concave on the nonnegative orthant, which is why
the box program is a second-order cone program. Proved by homogeneity and the superadditivity
`f(u) + f(v) ≤ f(u + v)` (Mahler), which is the arithmetic-geometric mean inequality applied to
`uᵢ / (uᵢ + vᵢ)`.

## Inputs
* `n` – dimension

## Hypotheses
* `hn` – dimension positive

## Conclusion
* the geometric mean is concave on the nonnegative orthant

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-B]: the geometric mean is concave on the nonnegative orthant. -/
theorem Zonotope.concaveOn_geomMean {n : ℕ} (hn : 0 < n) : -- --- CONCL ---
    ConcaveOn ℝ {γ : Fin n → ℝ | ∀ i, 0 ≤ γ i}
      (fun γ => (∏ i, γ i) ^ (1 / (n : ℝ))) := by -- --- PROOF ---
  -- the geometric mean, positively homogeneous
  have hz : (0 : ℝ) < 1 / n := by positivity
  have hhom : ∀ (t : ℝ) (γ : Fin n → ℝ), 0 ≤ t → (∀ i, 0 ≤ γ i) →
      (∏ i, (t • γ) i) ^ (1 / (n : ℝ)) = t * (∏ i, γ i) ^ (1 / (n : ℝ)) := by
    intro t γ ht hγ
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Real.mul_rpow (pow_nonneg ht n) (Finset.prod_nonneg fun i _ => hγ i), one_div,
      Real.pow_rpow_inv_natCast ht hn.ne']
  -- superadditivity, by the arithmetic-geometric mean inequality
  have hsup : ∀ u v : Fin n → ℝ, (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
      (∏ i, u i) ^ (1 / (n : ℝ)) + (∏ i, v i) ^ (1 / (n : ℝ))
        ≤ (∏ i, (u + v) i) ^ (1 / (n : ℝ)) := by
    intro u v hu hv
    by_cases hex : ∃ i, u i + v i = 0
    · -- a vanishing coordinate zeroes all three means
      obtain ⟨i, hi⟩ := hex
      have hpu : ∏ j, u j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by linarith [hu i, hv i])
      have hpv : ∏ j, v j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by linarith [hu i, hv i])
      rw [hpu, hpv, Real.zero_rpow hz.ne', add_zero]
      exact Real.rpow_nonneg (Finset.prod_nonneg fun j _ => add_nonneg (hu j) (hv j)) _
    · -- else the arithmetic-geometric mean inequality on `uᵢ / (uᵢ + vᵢ)` and `vᵢ / (uᵢ + vᵢ)`
      push Not at hex
      have hs : ∀ i, 0 < (u + v) i := fun i =>
        lt_of_le_of_ne (add_nonneg (hu i) (hv i)) (Ne.symm (hex i))
      have hP : 0 < ∏ i, (u + v) i := Finset.prod_pos fun i _ => hs i
      have hF := Real.rpow_pos_of_pos hP (1 / (n : ℝ))
      have hw : ∑ _i : Fin n, 1 / (n : ℝ) = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      -- `∏ (zᵢ)^{1/n} ≤ Σ zᵢ / n` for `z = u/(u+v)` and `v/(u+v)`
      have amgm : ∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) →
          (∏ i, w i) ^ (1 / (n : ℝ)) / (∏ i, (u + v) i) ^ (1 / (n : ℝ))
            ≤ ∑ i, 1 / (n : ℝ) * (w i / (u + v) i) := fun w hw0 => by
        have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (n : ℝ))
          (fun i => w i / (u + v) i) (fun _ _ => hz.le) hw
          (fun i _ => div_nonneg (hw0 i) (hs i).le)
        rwa [Real.finsetProd_rpow _ _ (fun i _ => div_nonneg (hw0 i) (hs i).le),
          Finset.prod_div_distrib, Real.div_rpow (Finset.prod_nonneg fun i _ => hw0 i) hP.le] at h
      have h1 := amgm u hu
      have h2 := amgm v hv
      -- the two bounds add to `Σ 1/n = 1`
      have hsum : ∑ i, 1 / (n : ℝ) * (u i / (u + v) i)
          + ∑ i, 1 / (n : ℝ) * (v i / (u + v) i) = 1 := by
        rw [← Finset.sum_add_distrib]
        refine (Finset.sum_congr rfl fun i _ => ?_).trans hw
        have := (hs i).ne'
        simp only [Pi.add_apply] at this ⊢
        field_simp
      have h3 : (∏ i, u i) ^ (1 / (n : ℝ)) / (∏ i, (u + v) i) ^ (1 / (n : ℝ))
          + (∏ i, v i) ^ (1 / (n : ℝ)) / (∏ i, (u + v) i) ^ (1 / (n : ℝ)) ≤ 1 := by linarith
      rw [← add_div] at h3
      exact (div_le_one hF).mp h3
  refine ⟨fun x hx y hy a b ha hb hab i => ?_, fun x hx y hy a b ha hb hab => ?_⟩
  · -- the orthant is convex
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  · -- homogeneity and superadditivity give concavity
    have h := hsup (a • x) (b • y) (fun i => mul_nonneg ha (hx i)) (fun i => mul_nonneg hb (hy i))
    rw [hhom a x ha hx, hhom b y hb hy] at h
    exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
