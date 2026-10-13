module

public import CORALean.Global.MeanValueAE

@[expose] public section

/-!
# Mean-value AE extensions of a robust range

[1, Thm. 2]: the robust range `range(f, x, I_A, I_E) = {z | ∀w ∈ x_A, ∃u ∈ x_E, z = f(w, u)}`
of `f` over `x = x_A × x_E` — `w` the disturbances, `u` the controls — lies between
`[f̄₀ - ⟨∇̲u, r(x_E)⟩ + ⟨∇̄w, r(x_A)⟩, f̲₀ + ⟨∇̲u, r(x_E)⟩ - ⟨∇̄w, r(x_A)⟩]` (4) and
`[f̲₀ - ⟨∇̄u, r(x_E)⟩ + ⟨∇̲w, r(x_A)⟩, f̄₀ + ⟨∇̄u, r(x_E)⟩ - ⟨∇̲w, r(x_A)⟩]` (3), where
`f(c(x)) ∈ f₀`, `|∇_w f(w, c(x_E))| ∈ ∇w` on `x_A` and `|∇_u f(w, u)| ∈ ∇u` on `x`.

The inputs are split as two vectors, `f w u`, rather than by index sets of one. Both
inclusions are [1, Thm. 1] twice, once in `w` at `u = c(x_E)` and once in `u` at each `w`;
the outer one needs `x_A` nonempty (over no disturbance every `z` is robustly reached),
the inner one `x_E`.

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. II-A.2]: the values `f` reaches for every disturbance `w ∈ x_A` with some
control `u ∈ x_E`. -/
def robustRange (f : (Fin p → ℝ) → (Fin q → ℝ) → ℝ) (loA hiA : Fin p → ℝ)
    (loE hiE : Fin q → ℝ) : Set ℝ :=
  {z | ∀ w ∈ Icc loA hiA, ∃ u ∈ Icc loE hiE, z = f w u}

/-- [1, Thm. 2] (3): the robust range is inside
`[f̲₀ - ⟨∇̄u, r_E⟩ + ⟨∇̲w, r_A⟩, f̄₀ + ⟨∇̄u, r_E⟩ - ⟨∇̲w, r_A⟩]`. -/
theorem robustMeanValueAE_outer {f : (Fin p → ℝ) → (Fin q → ℝ) → ℝ} {loA hiA : Fin p → ℝ}
    {loE hiE : Fin q → ℝ} (hA : loA ≤ hiA)
    (hfw : Differentiable ℝ fun w => f w fun j => (loE j + hiE j) / 2)
    (hfu : ∀ w, Differentiable ℝ (f w)) {f0lo f0hi : ℝ}
    (hf0 : f (fun i => (loA i + hiA i) / 2) (fun j => (loE j + hiE j) / 2) ∈ Icc f0lo f0hi)
    (dwlo : Fin p → ℝ) (hw : ∀ i, ∀ w ∈ Icc loA hiA,
      dwlo i ≤ |fderiv ℝ (fun w => f w fun j => (loE j + hiE j) / 2) w (Pi.single i 1)|)
    (duhi : Fin q → ℝ) (hu : ∀ w ∈ Icc loA hiA, ∀ j, ∀ u ∈ Icc loE hiE,
      |fderiv ℝ (f w) u (Pi.single j 1)| ≤ duhi j) :
    robustRange f loA hiA loE hiE
      ⊆ Icc (f0lo - ∑ j, duhi j * ((hiE j - loE j) / 2) + ∑ i, dwlo i * ((hiA i - loA i) / 2))
        (f0hi + ∑ j, duhi j * ((hiE j - loE j) / 2)
          - ∑ i, dwlo i * ((hiA i - loA i) / 2)) := by -- --- PROOF ---
  intro z hz
  -- the disturbances pushing `f(·, c_E)` furthest up and furthest down
  obtain ⟨wp, hwp, hfwp⟩ := exists_ge_add_sum_of_abs_partial_ge hfw hA dwlo
    fun i w hw' _ => hw i w hw'
  obtain ⟨wm, hwm, hfwm⟩ := exists_ge_add_sum_of_abs_partial_ge hfw.neg hA dwlo
    fun i w hw' _ => by rw [fderiv_neg, neg_apply, abs_neg]; exact hw i w hw'
  simp only [Pi.neg_apply] at hfwm
  -- against each, the control moves `f` by at most `⟨∇̄u, r_E⟩`
  obtain ⟨up, hup, rfl⟩ := hz wp hwp
  obtain ⟨um, hum, hzm⟩ := hz wm hwm
  have hp := abs_le.mp (abs_sub_le_sum_of_abs_partial_le (hfu wp) duhi
    (fun j u hu' _ => hu wp hwp j u hu') hup)
  have hm := abs_le.mp (abs_sub_le_sum_of_abs_partial_le (hfu wm) duhi
    (fun j u hu' _ => hu wm hwm j u hu') hum)
  exact ⟨by linarith [hf0.1], by linarith [hf0.2]⟩

/-- [1, Thm. 2] (4): `[f̄₀ - ⟨∇̲u, r_E⟩ + ⟨∇̄w, r_A⟩, f̲₀ + ⟨∇̲u, r_E⟩ - ⟨∇̄w, r_A⟩]` is inside
the robust range. -/
theorem robustMeanValueAE_inner {f : (Fin p → ℝ) → (Fin q → ℝ) → ℝ} {loA hiA : Fin p → ℝ}
    {loE hiE : Fin q → ℝ} (hE : loE ≤ hiE)
    (hfw : Differentiable ℝ fun w => f w fun j => (loE j + hiE j) / 2)
    (hfu : ∀ w, Differentiable ℝ (f w)) {f0lo f0hi : ℝ}
    (hf0 : f (fun i => (loA i + hiA i) / 2) (fun j => (loE j + hiE j) / 2) ∈ Icc f0lo f0hi)
    (dwhi : Fin p → ℝ) (hw : ∀ i, ∀ w ∈ Icc loA hiA,
      |fderiv ℝ (fun w => f w fun j => (loE j + hiE j) / 2) w (Pi.single i 1)| ≤ dwhi i)
    (dulo : Fin q → ℝ) (hu : ∀ w ∈ Icc loA hiA, ∀ j, ∀ u ∈ Icc loE hiE,
      dulo j ≤ |fderiv ℝ (f w) u (Pi.single j 1)|) :
    Icc (f0hi - ∑ j, dulo j * ((hiE j - loE j) / 2) + ∑ i, dwhi i * ((hiA i - loA i) / 2))
        (f0lo + ∑ j, dulo j * ((hiE j - loE j) / 2) - ∑ i, dwhi i * ((hiA i - loA i) / 2))
      ⊆ robustRange f loA hiA loE hiE := by -- --- PROOF ---
  intro z hz w hw'
  -- the disturbance moves `f(·, c_E)` by at most `⟨∇̄w, r_A⟩`
  have hwb := abs_le.mp (abs_sub_le_sum_of_abs_partial_le hfw dwhi
    (fun i w hw'' _ => hw i w hw'') hw')
  -- and against it the controls reach `f(w, c_E) ± ⟨∇̲u, r_E⟩`
  obtain ⟨u, hu', hfu'⟩ := meanValueAE_inner (hfu w) hE (f0lo := f w fun j => (loE j + hiE j) / 2)
    (f0hi := f w fun j => (loE j + hiE j) / 2) ⟨le_rfl, le_rfl⟩ dulo
    (fun j u hu'' _ => hu w hw' j u hu'') (show z ∈ _ from ⟨by linarith [hz.1, hf0.2],
      by linarith [hz.2, hf0.1]⟩)
  exact ⟨u, hu', hfu'.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
