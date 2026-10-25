module

public import CORALean.ContDynamics.LinearSys.Theorems.GirardReachOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsMemIUnionReachSetExactDistLe
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsMemInputReachDistLe

@[expose] public section

/-!
# [1, Alg. 1] converges

[1, Thm. 1], convergence, corrected: for `T = N r`, `N ≥ 1`,
`d_H(R_[0,T](I), R_{N-1}) ≤ r‖A‖e^{‖A‖T}(2µ/‖A‖ + (1/2 + r‖A‖) sup_{x∈I} ‖x‖)`. The printed proof's
recursion: a point of `Qᵢ₊₁ = e^{rA}Qᵢ + □(β_r)` is `e^{rA}q + w`; `q` is within `δᵢ` of some
`y ∈ Φ_t(I)` (induction), `w` within `µ‖A‖e^{r‖A‖}r²` of what a constant input reaches
(`exists_mem_inputReach_dist_le`, [1, Lemma 1]), and `e^{rA}y` plus that is in `Φ_{t+r}(I)`
(`reachSetExact_add_eq`). `δ₀` is [1, Lemma 2]'s, where the correction comes in: [1] prints
`(1/2 + r)`, which is false (`exists_lt_hausdorffDist_girardReach`). `sup_{x∈I} ‖x‖` is any bound
`s` on `I`'s norms: the algorithm uses the exact supremum (`isLUB_norm_image_fold_max_absBound`).

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

-- the window induction and the closed-form bookkeeping are elaborated in one proof
set_option maxHeartbeats 100000 in
/-- [1, Thm. 1], convergence, with `(1/2 + r‖A‖)` for the printed `(1/2 + r)`:
`d_H(R_[0,Nr](I), R_{N-1}) ≤ r‖A‖e^{‖A‖Nr}(2µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)`. -/
theorem LinearSys.hausdorffDist_girardReach_le (sys : LinearSys 𝕋 n) (I U : Zonotope (Vec ℝ n))
    {μ r s : ℝ} {N : ℕ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 < r) (hμ : 0 ≤ μ)
    (hU : U.construct = Metric.closedBall 0 μ) (hN : 1 ≤ N)
    (hs : ∀ z ∈ I.construct, ‖z‖ ≤ s) : -- --- CONCL ---
    Metric.hausdorffDist
      (⋃ t ∈ Set.Icc (0:ℝ) (N * r), sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) I U t)
      (⋃ Q ∈ sys.girardReach I μ r (N * r), Q.construct)
      ≤ r * ‖toRealMat sys.A‖ * Real.exp (‖toRealMat sys.A‖ * (N * r))
        * (2 * μ / ‖toRealMat sys.A‖
          + (1 / 2 + r * ‖toRealMat sys.A‖) * s) := by -- --- PROOF ---
  set A := toRealMat sys.A
  set a := ‖A‖
  set x := r * a with hxdef
  set E := exp (r • A)
  set β := (Real.exp x - 1) / a * μ
  set sA := Finset.univ.fold max 0 I.absBound
  set f : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) := fun Q => (Q.mtimes E).plus (Zonotope.cube n β)
  set Q₀ := (I.linComb (I.mtimes E)).plus
    (Zonotope.cube n ((Real.exp x - 1 - x) * sA + β))
  set δ₀ := x * Real.exp x * (μ / a + (1 / 2 + x) * sA)
  -- signs, and the algorithm's own `sup ‖x‖` against the bound `s`
  have hx0 : 0 < x := mul_pos hr hA
  have hex := Real.add_one_le_exp x
  have hβ0 : 0 ≤ β := mul_nonneg (div_nonneg (by linarith) hA.le) hμ
  have hsA : ∀ z ∈ I.construct, ‖z‖ ≤ sA := fun z hz =>
    (I.isLUB_norm_image_fold_max_absBound).1 ⟨z, hz, rfl⟩
  have hsAs : sA ≤ s := (I.isLUB_norm_image_fold_max_absBound).2 (by
    rintro _ ⟨z, hz, rfl⟩; exact hs z hz)
  have hsA0 : 0 ≤ sA := (norm_nonneg I.c).trans (hsA _ (Zonotope.center_mem_construct I))
  have hUb : Bornology.IsBounded (construct U) := Zonotope.isBounded_construct U
  have hUball : Metric.closedBall 0 μ ⊆ construct U := fun u hu => by
    show u ∈ U.construct; rw [hU]; exact hu
  -- the invariant: a point of `fⁱ(Q₀)` is near `Φ_t(I)` for a `t` in the `i`-th window
  have hrec : ∀ i : ℕ, ∀ q ∈ (f^[i] Q₀).construct, ∃ t ∈ Set.Icc ((i : ℝ) * r) ((i + 1) * r),
      ∃ y ∈ sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) I U t,
        dist q y ≤ Real.exp (i * x) * δ₀ + μ * r * Real.exp x * (Real.exp (i * x) - 1) := by
    intro i
    induction i with
    | zero =>
      intro q hq
      obtain ⟨y, hy, hd⟩ := sys.exists_mem_iUnion_reachSetExact_dist_le I U hA hr hμ hU hsA hq
      obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.mp hy
      refine ⟨t, by simpa using ht, y, hyt, ?_⟩
      simp only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul, sub_self, mul_zero, add_zero]
      exact hd
    | succ i ih =>
      -- a step: `q = e^{rA}q' + w`, `q'` near `y'` by induction
      intro q hq
      rw [Function.iterate_succ_apply'] at hq
      change q ∈ (((f^[i] Q₀).mtimes E).plus (Zonotope.cube n β)).construct at hq
      rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact, Zonotope.cube_exact n hβ0] at hq
      obtain ⟨_, ⟨q', hq', rfl⟩, w, hw, rfl⟩ := hq
      obtain ⟨t, ht, y', hy', hd'⟩ := ih q' hq'
      obtain ⟨v, hv, hdv⟩ := sys.exists_mem_inputReach_dist_le (S := 𝒵) (U := U) hA hr.le hμ hUball
        (mem_closedBall_zero_iff.mp hw)
      have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg i) hr.le).trans ht.1
      refine ⟨t + r, ⟨by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩,
        E *ᵥ y' + v, ?_, ?_⟩
      · rw [sys.reachSetExact_add_eq (S := 𝒵) I U ht0 hr.le hUb]
        exact ⟨_, ⟨y', hy', rfl⟩, v, hv, rfl⟩
      -- one step: `e^{rA}` stretches by at most `e^x`, the bloating adds Lemma 1's error
      have hE : dist (E *ᵥ q') (E *ᵥ y') ≤ Real.exp x * dist q' y' := by
        rw [dist_eq_norm, dist_eq_norm, ← Matrix.mulVec_sub]
        exact (Matrix.linfty_opNorm_mulVec _ _).trans
          (mul_le_mul_of_nonneg_right (MatExp.norm_exp_smul_le A hr.le) (norm_nonneg _))
      have hstep := (dist_add_add_le _ _ _ _).trans (add_le_add hE hdv)
      refine hstep.trans ?_
      have hexp : Real.exp (((i + 1 : ℕ) : ℝ) * x) = Real.exp (i * x) * Real.exp x := by
        rw [← Real.exp_add]; push_cast; ring_nf
      rw [hexp]
      have hD := mul_le_mul_of_nonneg_left hd' (Real.exp_pos x).le
      have hgap : 0 ≤ μ * r * Real.exp x * (Real.exp x - 1 - x) :=
        mul_nonneg (mul_nonneg (mul_nonneg hμ hr.le) (Real.exp_pos x).le) (by linarith)
      have halg : Real.exp x * (Real.exp (i * x) * δ₀
            + μ * r * Real.exp x * (Real.exp (i * x) - 1)) + μ * a * Real.exp x * r ^ 2
          + μ * r * Real.exp x * (Real.exp x - 1 - x)
          = Real.exp (i * x) * Real.exp x * δ₀
            + μ * r * Real.exp x * (Real.exp (i * x) * Real.exp x - 1) := by
        rw [hxdef]; ring
      linarith
  -- the windows are the `N` iterates, and the windows end by `N r`
  have hceil : ⌈(N * r : ℝ) / r⌉₊ - 1 + 1 = N := by
    rw [mul_div_cancel_right₀ _ hr.ne', Nat.ceil_natCast]; omega
  have hbound : 0 ≤ r * a * Real.exp (a * (N * r)) * (2 * μ / a + (1 / 2 + r * a) * s) := by
    have := (hsA0.trans hsAs)
    have := Real.exp_pos (a * (N * r))
    have := div_nonneg (mul_nonneg zero_le_two hμ) hA.le
    positivity
  refine Metric.hausdorffDist_le_of_mem_dist hbound
    (fun y hy => ⟨y, sys.girardReach_outer I U hA hr hμ hU hy, by rw [dist_self]; exact hbound⟩)
    (fun q hq => ?_)
  obtain ⟨Q, hQ, hqQ⟩ := Set.mem_iUnion₂.mp hq
  rw [sys.girardReach_eq, hceil] at hQ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
  have hiN : i + 1 ≤ N := List.mem_range.mp hi
  obtain ⟨t, ht, y, hy, hd⟩ := hrec i q hqQ
  have htT : t ≤ N * r := ht.2.trans (by
    have : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hiN
    nlinarith)
  refine ⟨y, Set.mem_iUnion₂.mpr ⟨t, ⟨(mul_nonneg (Nat.cast_nonneg i) hr.le).trans ht.1, htT⟩,
    hy⟩, hd.trans ?_⟩
  -- the invariant at `i ≤ N - 1`, against the closed form
  have hiN' : (i : ℝ) * x + x ≤ a * (N * r) := by
    have : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hiN
    rw [hxdef]; nlinarith
  have he1 : Real.exp (i * x) * Real.exp x ≤ Real.exp (a * (N * r)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hiN'
  have hδ : δ₀ ≤ x * Real.exp x * (μ / a + (1 / 2 + x) * s) := by
    have := Real.exp_pos x
    show x * Real.exp x * (μ / a + (1 / 2 + x) * sA) ≤ _
    gcongr
  -- the input term, and the total
  have hmu : μ * r * Real.exp x * (Real.exp (i * x) - 1)
      ≤ μ * r * (Real.exp (i * x) * Real.exp x) := by
    have hk := mul_nonneg (mul_nonneg hμ hr.le) (Real.exp_pos x).le
    calc μ * r * Real.exp x * (Real.exp (i * x) - 1)
        ≤ μ * r * Real.exp x * Real.exp (i * x) := mul_le_mul_of_nonneg_left (by linarith) hk
      _ = μ * r * (Real.exp (i * x) * Real.exp x) := by ring
  -- `e^{(i+1)x} ≤ e^{‖A‖T}` collects both terms
  have hfin : Real.exp (i * x) * (x * Real.exp x * (μ / a + (1 / 2 + x) * s))
      + μ * r * (Real.exp (i * x) * Real.exp x)
      ≤ r * a * Real.exp (a * (N * r)) * (2 * μ / a + (1 / 2 + r * a) * s) := by
    have hk : 0 ≤ r * a * (2 * μ / a + (1 / 2 + r * a) * s) := by
      have := hsA0.trans hsAs
      have := div_nonneg (mul_nonneg zero_le_two hμ) hA.le
      positivity
    have heq : Real.exp (i * x) * (x * Real.exp x * (μ / a + (1 / 2 + x) * s))
        + μ * r * (Real.exp (i * x) * Real.exp x)
        = (Real.exp (i * x) * Real.exp x) * (r * a * (2 * μ / a + (1 / 2 + r * a) * s)) := by
      rw [hxdef]; field_simp; ring
    rw [heq]
    calc (Real.exp (i * x) * Real.exp x) * (r * a * (2 * μ / a + (1 / 2 + r * a) * s))
        ≤ Real.exp (a * (N * r)) * (r * a * (2 * μ / a + (1 / 2 + r * a) * s)) :=
          mul_le_mul_of_nonneg_right he1 hk
      _ = r * a * Real.exp (a * (N * r)) * (2 * μ / a + (1 / 2 + r * a) * s) := by ring
  have hmono := mul_le_mul_of_nonneg_left hδ (Real.exp_pos (i * x)).le
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
