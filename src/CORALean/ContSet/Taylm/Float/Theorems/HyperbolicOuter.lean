module

public import CORALean.ContSet.Taylm.Float.Operations.Hyperbolic
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.Global.ElementaryDerivBounds
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.hyperbolic` encloses `sinh ∘ f` and `cosh ∘ f`

`taylor_remainder_abs_le` at `sinh` or `cosh`, whose derivatives alternate between the two, bounded
by `cosh` at the magnitude of the model. `hp` is `expUp`'s range hypothesis at that magnitude, as
`Taylm.exp_outer` keeps it; the magnitude is at least `|c|`, so it covers `sinhUp`, `sinhDown`,
`coshUp` at the center and `coshUp` at the magnitude itself.

## Inputs
* `p` – precision of the halvings
* `first` – flag for sinh instead of cosh
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hp` – the hull is small enough for the precision

## Conclusion
* the result encloses sinh or cosh of the function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The derivatives of `sinh` and `cosh` by parity. -/
private theorem aux_iteratedDeriv_hyp_parity (k : ℕ) : -- --- CONCL ---
    iteratedDeriv k Real.sinh = (if k % 2 = 0 then Real.sinh else Real.cosh) ∧
    iteratedDeriv k Real.cosh = (if k % 2 = 0 then Real.cosh else Real.sinh) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih.1, ih.2]
    by_cases h : k % 2 = 0
    · have h' : ¬ (k + 1) % 2 = 0 := by omega
      simp [h, h', Real.deriv_sinh, Real.deriv_cosh]
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h', Real.deriv_sinh, Real.deriv_cosh]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.hyperbolic_outer (p : ℕ) (first : Bool) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ}
    (h : T.Encloses f)
    (hp : toReal (maximum (absolute T.constCoef) (maximum (absolute T.bounds.inf)
      (absolute T.bounds.sup))) ≤ 2 ^ p / 2) : -- --- CONCL ---
    (T.hyperbolic p first).Encloses
      fun t => (if first then Real.sinh else Real.cosh) (f t) := by -- --- PROOF ---
  -- the center, the order, and the function whose Taylor model this is
  set c := T.constCoef
  set N := T.maxOrder
  set g : ℝ → ℝ := if first then Real.sinh else Real.cosh with hg_def
  -- the magnitude bound, as stored and as a real number
  set Mf : 𝕋 := maximum (absolute c) (maximum (absolute T.bounds.inf) (absolute T.bounds.sup))
  set M : ℝ := max |toReal c| (max |toReal T.bounds.inf| |toReal T.bounds.sup|) with hM
  have hm : toReal Mf = M := by
    rw [toReal_maximum, toReal_maximum, toReal_absolute, toReal_absolute, toReal_absolute]
  have hB0 : (0 : ℝ) ≤ 2 ^ p / 2 := by positivity
  have hcm : |toReal c| ≤ 2 ^ p / 2 :=
    le_trans (le_max_left _ _) (hm ▸ hp)
  have hc1 : toReal c ≤ 2 ^ p / 2 := le_trans (le_abs_self _) hcm
  have hc2 : -toReal c ≤ 2 ^ p / 2 := le_trans (neg_le_abs _) hcm
  -- the derivatives of `g` at the center, by parity
  have hder : ∀ k : ℕ, iteratedDeriv k g (toReal c) =
      if (k % 2 == 0) == first then Real.sinh (toReal c) else Real.cosh (toReal c) := by
    intro k
    obtain ⟨h1, h2⟩ := aux_iteratedDeriv_hyp_parity k
    cases first <;> simp [hg_def, h1, h2] <;> split_ifs <;> simp_all
  -- `g` is smooth, and its next derivative is bounded by `cosh` of the magnitude
  have hgd : ContDiff ℝ (N + 1) g := by
    cases first
    · simpa [hg_def] using Real.contDiff_cosh
    · simpa [hg_def] using Real.contDiff_sinh
  have hbd : ∀ ξ : ℝ, |ξ| ≤ M →
      |iteratedDeriv (N + 1) g ξ| ≤
        Real.cosh (M) := by
    intro ξ hξ
    cases first
    · simpa [hg_def] using abs_iteratedDeriv_cosh_le (N + 1) hξ
    · simpa [hg_def] using abs_iteratedDeriv_sinh_le (N + 1) hξ
  -- the coefficients: `sinh c` or `cosh c` by parity, between its two roundings
  have hbase : ∀ k : ℕ, toReal (((if (k % 2 == 0) == first then ⟨sinhDown p c, sinhUp p c⟩
      else ⟨coshDown p c, coshUp p c⟩) : Interval 𝕋).inf) ≤ iteratedDeriv k g (toReal c) ∧
      iteratedDeriv k g (toReal c) ≤ toReal (((if (k % 2 == 0) == first then
        ⟨sinhDown p c, sinhUp p c⟩ else ⟨coshDown p c, coshUp p c⟩) : Interval 𝕋).sup) := by
    intro k
    rw [hder k]
    split_ifs
    · exact ⟨sinhDown_le p c hc2, sinhUp_ge p c hc1⟩
    · exact ⟨coshDown_le p c, coshUp_ge p c hc1 hc2⟩
  have hF1 := fun k => divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) k
  refine Taylm.compose_outer h g c _ _ N _
    (fun k => iteratedDeriv k g (toReal c) / (k.factorial : ℝ)) (fun k _ => ?_) fun t ht => ?_
  · -- coefficient `s * (1 / k!)` between the corner products
    have hb := hbase k
    have hf := hF1 k
    have hs := Real.Interval.mul_between_corners hb.1 hb.2 hf.1 hf.2
    rw [← div_eq_mul_one_div] at hs
    exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hs.1, le_trans hs.2 (Interval.le_mulHi _ _ _ _)⟩
  · have hb := Taylm.bounds_mem h ht
    -- every point of the hull of the center and the box is below the magnitude
    have hmag : ∀ ξ ∈ Set.Icc (min (toReal c) (toReal T.bounds.inf))
        (max (toReal c) (toReal T.bounds.sup)),
        |ξ| ≤ M := by
      intro ξ hξ
      have h1 : |toReal c| ≤ M := le_max_left _ _
      have h2 := le_max_left |toReal T.bounds.inf| |toReal T.bounds.sup|
      have h3 := le_max_right |toReal T.bounds.inf| |toReal T.bounds.sup|
      have h4 : max |toReal T.bounds.inf| |toReal T.bounds.sup| ≤ M := le_max_right _ _
      rw [abs_le]
      constructor
      · rcases min_le_iff.1 hξ.1 with h5 | h5
        · linarith [neg_abs_le (toReal c)]
        · linarith [neg_abs_le (toReal T.bounds.inf)]
      · rcases le_max_iff.1 hξ.2 with h5 | h5
        · linarith [le_abs_self (toReal c)]
        · linarith [le_abs_self (toReal T.bounds.sup)]
    -- Lagrange at the center, the derivative bounded by `cosh` of the magnitude
    have hsub : Set.uIcc (toReal c) (f t) ⊆
        Set.Icc (min (toReal c) (toReal T.bounds.inf)) (max (toReal c) (toReal T.bounds.sup)) :=
      Set.uIcc_subset_Icc ⟨min_le_left _ _, le_max_left _ _⟩
        ⟨le_trans (min_le_right _ _) hb.1, le_trans hb.2 (le_max_right _ _)⟩
    have hL := taylor_remainder_abs_le (g := g) (N := N) (c := toReal c) (x := f t)
      (D := Real.cosh (M))
      (fun ξ _ => hgd.contDiffAt) fun ξ hξ => hbd ξ (hmag ξ (hsub hξ))
    refine le_trans hL ?_
    -- each factor of the bound below its rounded counterpart
    set B : 𝕋 := maximum zero (maximum (subUp T.bounds.sup c) (subUp c T.bounds.inf))
    have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
    have hPow := le_powUp (abs_nonneg _) hB (N + 1)
    -- the derivative bound, `cosh` of the magnitude, below its rounding
    have hD : Real.cosh (M)
        ≤ toReal (coshUp p Mf) := by
      rw [← hm]
      have hm0 : -M ≤ 2 ^ p / 2 := by
        have : |toReal c| ≤ M := le_max_left _ _
        have := abs_nonneg (toReal c)
        linarith
      exact coshUp_ge p _ hp (by rw [hm]; exact hm0)
    -- `1 / (N+1)!` below its rounding
    have hF := (divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
      (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
    have hE := Real.cosh_pos (M)
    have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
    have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
    calc Real.cosh (M) *
          |f t - toReal c| ^ (N + 1) / ((N + 1).factorial : ℝ)
        = Real.cosh (M) *
          |f t - toReal c| ^ (N + 1) * (1 / ((N + 1).factorial : ℝ)) := by ring
      _ ≤ toReal (coshUp p (maximum (absolute c) (maximum (absolute T.bounds.inf)
            (absolute T.bounds.sup)))) * toReal (powUp B (N + 1))
          * toReal (divFact ⟨(one : 𝕋), (one : 𝕋)⟩ (N + 1)).sup := by
        apply mul_le_mul (mul_le_mul hD hPow hY (le_trans hE.le hD)) hF hFpos
        exact mul_nonneg (le_trans hE.le hD) (le_trans hY hPow)
      _ ≤ toReal (mulUp (coshUp p (maximum (absolute c) (maximum (absolute T.bounds.inf)
            (absolute T.bounds.sup)))) (powUp B (N + 1)))
          * toReal (divFact ⟨(one : 𝕋), (one : 𝕋)⟩ (N + 1)).sup := by
        apply mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) (le_trans hFpos hF)
      _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
