module

public import CORALean.ContSet.HPolytope.Real.Definitions.NaiveHalfspaceValue
public import CORALean.ContSet.HPolytope.Real.Theorems.IsGreatestPolyNormEllipsotope

@[expose] public section

/-!
# Naive halfspace sampling under-approximates

`[1, Eq. 12]`: `r_hs = maxᵢ ‖G'ᵀ λ_{jᵢ}‖_{p*} / |b_{jᵢ}| ≤ r(Ê, Ẑ)` for any sampled facets of
`Z(H)`, which is a representation closed under `λ ↦ -λ` as every zonotope's is. The printed
norm of the pair `(Gᵀλ, λᵀ(c - d))` is at most the sum of the two (`Eq. 11`'s support
function), and the sum over a facet and its mirror is the exact radius
(`HPolytope.isGreatest_polyNorm_ellipsotope`), so the printed quantity is below the radius.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ENNReal

variable {n s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.naiveHalfspaceValue_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (G : E →ₗ[ℝ] Vec ℝ n)
    (c d : Vec ℝ n) {Λ : Mat ℝ s n} {b : Vec ℝ s} (hb : ∀ i, 0 < b i)
    (hsym : ∀ i, ∃ i', (∀ x, (Λ *ᵥ x) i' = -(Λ *ᵥ x) i) ∧ b i' = b i) {r : ℝ}
    (hr : IsGreatest ((fun α => HPolytope.polyNorm Λ b (G α + c - d)) '' Metric.closedBall 0 1) r)
    {N : ℕ} (hN : 0 < N) (j : Fin N → Fin s) :
    HPolytope.naiveHalfspaceValue p G c d Λ b hN j ≤ r := by -- --- PROOF ---
  set f := fun i => LinearMap.toContinuousLinearMap ((HPolytope.rowLin Λ i).comp G) with hf
  set T := insert 0 (Finset.univ.image fun i =>
    (‖f i‖ + (Λ *ᵥ (c - d)) i) / b i) with hT
  -- the exact radius is the largest of the terms
  have hrT : r = T.max' (Finset.insert_nonempty _ _) :=
    hr.unique (HPolytope.isGreatest_polyNorm_ellipsotope G c d hb)
  have hterm : ∀ i, (‖f i‖ + (Λ *ᵥ (c - d)) i) / b i ≤ r := fun i => by
    rw [hrT]
    exact T.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine Finset.sup'_le _ _ fun k _ => ?_
  set i := j k
  -- the pair's norm is at most the sum of its parts
  have hsum : ‖HPolytope.extendedRow p G c d Λ i‖ ≤ ‖f i‖ + |(Λ *ᵥ (c - d)) i| := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have hx : HPolytope.extendedRow p G c d Λ i x
        = f i x.fst + x.snd * (Λ *ᵥ (c - d)) i := by
      simp [HPolytope.extendedRow, hf, HPolytope.rowLin, mulVec_add, mulVec_smul]
    rw [hx]
    calc _ ≤ |f i x.fst| + |x.snd * (Λ *ᵥ (c - d)) i| := abs_add_le _ _
      _ ≤ ‖f i‖ * ‖x.fst‖ + ‖x.snd‖ * |(Λ *ᵥ (c - d)) i| := by
        rw [abs_mul]
        exact add_le_add (by simpa using (f i).le_opNorm x.fst) (by simp)
      _ ≤ _ := by
        have h1 := WithLp.norm_fst_le (x := x)
        have h2 := WithLp.norm_snd_le (x := x)
        nlinarith [norm_nonneg (f i), abs_nonneg ((Λ *ᵥ (c - d)) i), norm_nonneg x]
  rw [abs_of_pos (hb i), div_le_iff₀ (hb i)]
  -- the absolute value is the term at the row or at its mirror
  rcases le_total 0 ((Λ *ᵥ (c - d)) i) with h0 | h0
  · rw [abs_of_nonneg h0] at hsum
    exact hsum.trans (by simpa [div_le_iff₀ (hb i)] using hterm i)
  · obtain ⟨i', hm, hbi⟩ := hsym i
    have hfi : ‖f i'‖ = ‖f i‖ := by
      rw [show f i' = -f i from ContinuousLinearMap.ext fun α => by
        simp [hf, HPolytope.rowLin, hm]]
      exact norm_neg _
    rw [abs_of_nonpos h0] at hsum
    have := hterm i'
    rw [hbi, div_le_iff₀ (hb i), hfi, hm] at this
    exact hsum.trans (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
