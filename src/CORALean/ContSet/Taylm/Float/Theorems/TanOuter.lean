module

public import CORALean.ContSet.Taylm.Float.Operations.Tan
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Interval.Float.Theorems.EvalPolyCoeffsMem
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.Global.ElementaryDerivBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.tan` encloses `tan ∘ f`

`taylor_remainder_abs_le` at `tan`, whose derivatives are `odePoly (1 + X²) k` at `tan`
(`iteratedDeriv_of_ode`) and are bounded by the same polynomial of order `N+1` at `tan m`
(`abs_iteratedDeriv_tan_le`), `m` the magnitude of the model. The integer polynomial lists
evaluate as the real ones (`eval_odePoly_odeL`), and `Interval.evalPolyCoeffs_mem` encloses them.
The domain is explicit: the magnitude below `π/2`, and the cosine certified positive by
`cosDown` at the center and at the magnitude, which is what `tanDown_le` and `le_tanUp` need.

## Inputs
* `p` – precision of the halvings
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hπ` – the hull stays below half of pi
* `hcc` – cosine at the center is positive
* `hcm` – cosine at the hull's magnitude is positive

## Conclusion
* the result encloses tangent of the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Polynomial

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.tan_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hπ : toReal (maximum (absolute T.constCoef) (maximum (absolute T.bounds.inf)
      (absolute T.bounds.sup))) < Real.pi / 2)
    (hcc : 0 < toReal (cosDown p T.constCoef))
    (hcm : 0 < toReal (cosDown p (maximum (absolute T.constCoef) (maximum (absolute T.bounds.inf)
      (absolute T.bounds.sup))))) : -- --- CONCL ---
    (T.tan p).Encloses fun t => Real.tan (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  set m : 𝕋 :=
    maximum (absolute c) (maximum (absolute T.bounds.inf) (absolute T.bounds.sup)) with hm_def
  have hm : toReal m = max |toReal c| (max |toReal T.bounds.inf| |toReal T.bounds.sup|) := by
    rw [hm_def, toReal_maximum, toReal_maximum, toReal_absolute, toReal_absolute,
      toReal_absolute]
  set M := toReal m with hM
  -- every point of the hull of the center and the box is below the magnitude
  have hmag : ∀ ξ ∈ Set.Icc (min (toReal c) (toReal T.bounds.inf))
      (max (toReal c) (toReal T.bounds.sup)), |ξ| ≤ M := by
    intro ξ hξ
    have h1 := le_max_left |toReal c| (max |toReal T.bounds.inf| |toReal T.bounds.sup|)
    have h2 := le_max_left |toReal T.bounds.inf| |toReal T.bounds.sup|
    have h3 := le_max_right |toReal T.bounds.inf| |toReal T.bounds.sup|
    have h4 := le_max_right |toReal c| (max |toReal T.bounds.inf| |toReal T.bounds.sup|)
    rw [hm] at *
    rw [abs_le]
    constructor
    · rcases min_le_iff.1 hξ.1 with h5 | h5
      · linarith [neg_abs_le (toReal c)]
      · linarith [neg_abs_le (toReal T.bounds.inf)]
    · rcases le_max_iff.1 hξ.2 with h5 | h5
      · linarith [le_abs_self (toReal c)]
      · linarith [le_abs_self (toReal T.bounds.sup)]
  have hcM : |toReal c| ≤ M := by rw [hm]; exact le_max_left _ _
  -- the derivatives of `tan` at the center are the integer polynomial at `tan c`
  have hcdom : toReal c ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have := abs_lt.1 (lt_of_le_of_lt hcM hπ)
    exact ⟨this.1, this.2⟩
  have hder : ∀ k : ℕ, iteratedDeriv k Real.tan (toReal c) =
      evalL (odeL [1, 0, 1] k) (Real.tan (toReal c)) := by
    intro k
    rw [iteratedDeriv_of_ode (g := Real.tan) (U := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
      isOpen_Ioo (q := 1 + X ^ 2) (fun y hy => by
        have hc : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo hy).ne'
        simpa [one_div, ← Real.inv_one_add_tan_sq hc] using Real.hasDerivAt_tan hc) k _ hcdom]
    exact eval_odePoly_odeL (q := [1, 0, 1]) (fun x => by simp [evalL]; ring) k _
  have ht1 := tanDown_le p c hcc
  have ht2 := le_tanUp p c hcc
  have hF1 := fun k => divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) k
  refine Taylm.compose_outer h Real.tan c _ _ N _
    (fun k => iteratedDeriv k Real.tan (toReal c) / (k.factorial : ℝ)) (fun k _ => ?_)
    fun t ht => ?_
  · -- coefficient `P(tan c) * (1 / k!)` between the corner products
    have hb := Interval.evalPolyCoeffs_mem ht1 ht2 (odeL [1, 0, 1] k)
    have hf := hF1 k
    have hs := Real.Interval.mul_between_corners hb.1 hb.2 hf.1 hf.2
    rw [← div_eq_mul_one_div, ← hder k] at hs
    exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hs.1, le_trans hs.2 (Interval.le_mulHi _ _ _ _)⟩
  · have hb := Taylm.bounds_mem h ht
    have hsub : Set.uIcc (toReal c) (f t) ⊆
        Set.Icc (min (toReal c) (toReal T.bounds.inf)) (max (toReal c) (toReal T.bounds.sup)) :=
      Set.uIcc_subset_Icc ⟨min_le_left _ _, le_max_left _ _⟩
        ⟨le_trans (min_le_right _ _) hb.1, le_trans hb.2 (le_max_right _ _)⟩
    -- Lagrange at the center, the derivative bounded by the polynomial at `tan M`
    have hD1 : ∀ ξ ∈ Set.uIcc (toReal c) (f t), |iteratedDeriv (N + 1) Real.tan ξ| ≤
        evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M) := fun ξ hξ => by
      rw [← eval_odePoly_odeL (q := [1, 0, 1]) (Q := 1 + X ^ 2)
        (fun x => by simp [evalL]; ring) _ (Real.tan M)]
      exact abs_iteratedDeriv_tan_le _ (hmag ξ (hsub hξ)) hπ
    have hL := taylor_remainder_abs_le (g := Real.tan) (N := N) (c := toReal c)
      (x := f t) (D := evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M))
      (fun ξ hξ => by
        have hm' := lt_of_le_of_lt (hmag ξ (hsub hξ)) hπ
        rw [abs_lt] at hm'
        exact Real.contDiffAt_tan.2 (Real.cos_pos_of_mem_Ioo ⟨hm'.1, hm'.2⟩).ne') hD1
    refine le_trans hL ?_
    -- each factor of the bound below its rounded counterpart
    set B : 𝕋 := maximum zero (maximum (subUp T.bounds.sup c) (subUp c T.bounds.inf))
    have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
    have hPow := le_powUp (abs_nonneg _) hB (N + 1)
    -- the derivative bound below its rounding
    have hD : evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M) ≤
        toReal (Interval.evalPolyCoeffs (tanDown p m) (tanUp p m) (odeL [1, 0, 1] (N + 1))).sup :=
      (Interval.evalPolyCoeffs_mem (tanDown_le p m hcm) (le_tanUp p m hcm) _).2
    -- the bound is non-negative, being above an absolute value
    have hE : 0 ≤ evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M) :=
      le_trans (abs_nonneg _) (hD1 (toReal c) Set.left_mem_uIcc)
    -- `1 / (N+1)!` below its rounding
    have hF := (divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
      (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
    have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
    have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
    calc evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M) * |f t - toReal c| ^ (N + 1)
          / ((N + 1).factorial : ℝ)
        = evalL (odeL [1, 0, 1] (N + 1)) (Real.tan M) * |f t - toReal c| ^ (N + 1)
          * (1 / ((N + 1).factorial : ℝ)) := by ring
      _ ≤ toReal (Interval.evalPolyCoeffs (tanDown p m) (tanUp p m) (odeL [1, 0, 1] (N + 1))).sup
            * toReal (powUp B (N + 1))
          * toReal (divFact ⟨(one : 𝕋), (one : 𝕋)⟩ (N + 1)).sup := by
        apply mul_le_mul (mul_le_mul hD hPow hY (le_trans hE hD)) hF hFpos
        exact mul_nonneg (le_trans hE hD) (le_trans hY hPow)
      _ ≤ toReal (mulUp (Interval.evalPolyCoeffs (tanDown p m) (tanUp p m)
              (odeL [1, 0, 1] (N + 1))).sup (powUp B (N + 1)))
          * toReal (divFact ⟨(one : 𝕋), (one : 𝕋)⟩ (N + 1)).sup := by
        apply mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) (le_trans hFpos hF)
      _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
