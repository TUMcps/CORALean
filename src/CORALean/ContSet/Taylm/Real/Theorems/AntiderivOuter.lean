import CORALean.ContSet.Taylm.Real.Operations.Antideriv
import CORALean.ContSet.Taylm.Real.Theorems.IntegralPolyOf
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfFilter

/-!
# `Taylm.antideriv` encloses the antiderivative

[1, Def. 3 (antiderivation)] with the corrected remainder: for `f` continuous along the
coordinate lines, `antideriv i` encloses `t ↦ ∫₀^{tᵢ} f(t with tᵢ := s) ds`. On the segment from
`0` to `tᵢ`, which stays in the box, `f - P_{n-1}` lies in `J`, so its integral is at most
`max |J|·|tᵢ| ≤ max |J|` in magnitude, and `J·[-1, 1]` is `[-max |J|, max |J|]`; the integral of
`P_{n-1}` is `integrateTerms` exactly (`integral_polyOf`).

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.antideriv_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (i : Fin n)
    (hf : ∀ t ∈ Taylm.box n, ContinuousOn (fun s => f (Function.update t i s)) (Set.Icc (-1) 1)) :
    (T.antideriv i).Encloses fun t =>
      ∫ s in (0 : ℝ)..t i, f (Function.update t i s) := by -- --- PROOF ---
  intro t ht
  set Plow := T.terms.filter fun a => Nat.blt (Taylm.degree a.2) T.maxOrder
  set Prest := T.terms.filter fun a => !Nat.blt (Taylm.degree a.2) T.maxOrder
  set J := ((Taylm.polyBounds Prest).1 + T.remInf, (Taylm.polyBounds Prest).2 + T.remSup)
  have hti := abs_le.1 (ht i)
  -- the segment from `0` to `tᵢ` stays in the box
  have hseg : ∀ s ∈ Set.uIcc (0 : ℝ) (t i), Function.update t i s ∈ Taylm.box n ∧
      s ∈ Set.Icc (-1 : ℝ) 1 := by
    intro s hs
    have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := by
      rcases Set.mem_uIcc.1 hs with h | h <;> constructor <;> linarith [h.1, h.2]
    refine ⟨fun k => ?_, hs'⟩
    by_cases hk : k = i
    · subst hk; simp only [Function.update_self]; exact abs_le.2 hs'
    · rw [Function.update_of_ne hk]; exact ht k
  -- on it, `f - P_{n-1}` lies in `J`
  have hJ : ∀ s ∈ Set.uIcc (0 : ℝ) (t i),
      J.1 ≤ f (Function.update t i s) - Taylm.polyOf Plow (Function.update t i s) ∧
      f (Function.update t i s) - Taylm.polyOf Plow (Function.update t i s) ≤ J.2 := by
    intro s hs
    obtain ⟨hb, -⟩ := hseg s hs
    have hr := h _ hb
    have hq := Taylm.polyBounds_mem Prest hb
    have hsplit := Taylm.polyOf_filter T.terms
      (fun a => Nat.blt (Taylm.degree a.2) T.maxOrder) (Function.update t i s)
    simp only [Taylm.poly] at hr
    simp only [J]
    constructor <;> linarith [hr.1, hr.2, hq.1, hq.2]
  -- so its magnitude is at most `M`
  set M := max |J.1| |J.2|
  have hM : ∀ s ∈ Set.uIoc (0 : ℝ) (t i),
      ‖f (Function.update t i s) - Taylm.polyOf Plow (Function.update t i s)‖ ≤ M := by
    intro s hs
    have := hJ s (Set.uIoc_subset_uIcc hs)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le J.1, le_max_left |J.1| |J.2|]
    · linarith [le_abs_self J.2, le_max_right |J.1| |J.2|]
  -- integrability of both pieces
  have hfi : IntervalIntegrable (fun s => f (Function.update t i s))
      MeasureTheory.volume 0 (t i) :=
    ((hf t ht).mono fun s hs => (hseg s hs).2).intervalIntegrable
  have hpi : IntervalIntegrable (fun s => Taylm.polyOf Plow (Function.update t i s))
      MeasureTheory.volume 0 (t i) :=
    ((Taylm.continuous_polyOf Plow).comp
      (continuous_const.update i continuous_id)).intervalIntegrable _ _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hM
  rw [intervalIntegral.integral_sub hfi hpi, Taylm.integral_polyOf] at hint
  have hlen : |t i - 0| ≤ 1 := by rw [sub_zero]; exact ht i
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hb : |(∫ s in (0 : ℝ)..t i, f (Function.update t i s)) -
      Taylm.polyOf (Taylm.integrateTerms i Plow) t| ≤ M := by
    rw [← Real.norm_eq_abs]
    exact le_trans hint (by nlinarith)
  -- `J·[-1, 1]` is `[-M, M]`
  have hlo : Interval.mulLo J.1 J.2 (-1) 1 = -M := by
    simp only [Interval.mulLo, M]
    rcases le_total 0 J.1 with h1 | h1 <;> rcases le_total 0 J.2 with h2 | h2 <;>
      simp [abs_of_nonneg, abs_of_nonpos, h1, h2, min_def, max_def] <;> split_ifs <;> linarith
  have hhi : Interval.mulHi J.1 J.2 (-1) 1 = M := by
    simp only [Interval.mulHi, M]
    rcases le_total 0 J.1 with h1 | h1 <;> rcases le_total 0 J.2 with h2 | h2 <;>
      simp [abs_of_nonneg, abs_of_nonpos, h1, h2, max_def]
  simp only [Taylm.antideriv, Taylm.poly]
  rw [hlo, hhi]
  exact abs_le.1 hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
