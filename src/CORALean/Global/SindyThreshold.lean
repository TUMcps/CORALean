import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod

/-!
# Sequential thresholded least squares

[1, Alg. 1], the paper's `Code 1` of Sec. 3.1: start from the least-squares solution `Θ \ Ẋ`,
then `K = 10` times find the coefficients with `|ξ| < λ`, set them to zero and regress the
dynamics of each column onto the remaining terms. `Θ(:,biginds) \ Ẋ(:,ind)` is the argument
`solve ind S`, the regression onto the terms `S`, of which only the entries in `S` are read: a
solver, not computed here. Written for any number of iterations `K`; `sindy 10` is the printed
code.

For `λ > 0` and any solver the iteration is monotone: a coefficient that is zero stays zero
(the terms of `S` shrink), so after at most `p · n + 1` iterations (`p` terms, `n` columns) the
iterate is a fixed point, which is what [1, Sec. 3.1] says as "continued until the non-zero
coefficients converge". At a fixed point every coefficient is zero or at least `λ` in
magnitude, and the nonzero ones are the regression onto the surviving terms; if `solve`
satisfies the normal equations of its regression so does the fixed point, on its support.
Nothing is claimed about *which* support results, about the number of iterations the paper
calls small (`p · n + 1` is what is proved, `10` is what is printed), or for `λ ≤ 0`, where
nothing is thresholded.

## References

* [1] S. L. Brunton, J. L. Proctor and J. N. Kutz. "Discovering governing equations from data by
      sparse identification of nonlinear dynamical systems". Proceedings of the National
      Academy of Sciences, 113(15):3932-3937, 2016 (arXiv:1509.03580).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m p n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One pass of the loop of `Code 1`: threshold at `λ` (`smallinds`, `Xi(smallinds) = 0`), then
regress each column onto its `biginds`. -/
noncomputable def sindyStep (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (Ξ : Mat ℝ p n) : Mat ℝ p n :=
  let small := fun j c => |Ξ j c| < lam                                -- smallinds
  let Ξt := Matrix.of fun j c => if small j c then 0 else Ξ j c        -- Xi(smallinds) = 0
  let big := fun c => Finset.univ.filter fun j => ¬ small j c          -- biginds, column `ind`
  Matrix.of fun j c => if small j c then Ξt j c else solve c (big c) j -- Xi(biginds,ind) = ...

/-- `Code 1` with `K` passes: `Xi = Theta \ dXdt`, then `for k = 1:K`. -/
noncomputable def sindy (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ) (K : ℕ) :
    Mat ℝ p n :=
  let Ξ₀ := Matrix.of fun j c => solve c Finset.univ j                 -- Xi = Theta \ dXdt
  (sindyStep lam solve)^[K] Ξ₀

/-- The entries not thresholded away by `λ`. -/
noncomputable def sindyBig (lam : ℝ) (Ξ : Mat ℝ p n) : Finset (Fin p × Fin n) :=
  Finset.univ.filter fun jc => lam ≤ |Ξ jc.1 jc.2|

/-- A pass keeps only entries that were not thresholded, so for `λ > 0` it only removes
nonzero entries. -/
theorem sindyBig_step_subset (lam : ℝ) (hlam : 0 < lam)
    (solve : Fin n → Finset (Fin p) → Fin p → ℝ) (Ξ : Mat ℝ p n) :
    sindyBig lam (sindyStep lam solve Ξ) ⊆ sindyBig lam Ξ := by -- --- PROOF ---
  intro jc hjc
  simp only [sindyBig, Finset.mem_filter, Finset.mem_univ, true_and] at hjc ⊢
  by_contra hsmall
  push Not at hsmall
  have : sindyStep lam solve Ξ jc.1 jc.2 = 0 := by simp [sindyStep, hsmall]
  rw [this, abs_zero] at hjc
  exact absurd hjc (not_le.mpr hlam)

/-- A pass depends on its argument only through the entries at least `λ` in magnitude. -/
theorem sindyStep_congr (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (Ξ Ξ' : Mat ℝ p n) (h : sindyBig lam Ξ = sindyBig lam Ξ') :
    sindyStep lam solve Ξ = sindyStep lam solve Ξ' := by -- --- PROOF ---
  have hiff : ∀ j c, (|Ξ j c| < lam) ↔ (|Ξ' j c| < lam) := fun j c => by
    have := Finset.ext_iff.mp h (j, c)
    simp only [sindyBig, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [← not_le, ← not_le, this]
  ext j c
  simp only [sindyStep, Matrix.of_apply]
  by_cases hs : |Ξ j c| < lam
  · simp [hs, (hiff j c).mp hs]
  · have hs' : ¬ |Ξ' j c| < lam := fun h' => hs ((hiff j c).mpr h')
    have hset : (Finset.univ.filter fun j => ¬ |Ξ j c| < lam)
        = Finset.univ.filter fun j => ¬ |Ξ' j c| < lam := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_congr (hiff i c)
    simp only [hs, hs', if_false]
    rw [hset]

/-- A pass that thresholds nothing further is a fixed point: if `Ξ'` is the pass applied to `Ξ`
and has the same surviving entries, the pass leaves `Ξ'` as it is. -/
theorem sindyStep_fixed_of_big_eq (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (Ξ : Mat ℝ p n) (h : sindyBig lam (sindyStep lam solve Ξ) = sindyBig lam Ξ) :
    sindyStep lam solve (sindyStep lam solve Ξ) = sindyStep lam solve Ξ :=
  sindyStep_congr lam solve _ _ h

/-- [1, Sec. 3.1]: for `λ > 0`, `K ≥ p · n + 1` passes of `Code 1` reach a fixed point, whatever
the solver and the number of passes beyond. -/
theorem sindy_fixed (lam : ℝ) (hlam : 0 < lam) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (K : ℕ) (hK : p * n + 1 ≤ K) :
    sindyStep lam solve (sindy lam solve K) = sindy lam solve K := by -- --- PROOF ---
  set f := sindyStep lam solve with hf
  set Ξ₀ : Mat ℝ p n := Matrix.of fun j c => solve c Finset.univ j with hΞ₀
  set b : ℕ → Finset (Fin p × Fin n) := fun t => sindyBig lam (f^[t] Ξ₀) with hb
  have hsub : ∀ t, b (t + 1) ⊆ b t := fun t => by
    simp only [hb, Function.iterate_succ_apply']
    exact sindyBig_step_subset lam hlam solve _
  -- strict decrease at every pass would empty the set within `p * n + 1` passes
  have hcount : ∀ T, (∀ t < T, b (t + 1) ≠ b t) → (b T).card + T ≤ (b 0).card := by
    intro T
    induction T with
    | zero => intro _; simp
    | succ T ih =>
      intro h
      have h1 := ih fun t ht => h t (Nat.lt_succ_of_lt ht)
      have h2 : (b (T + 1)).card < (b T).card :=
        Finset.card_lt_card (lt_of_le_of_ne (hsub T) (h T (Nat.lt_succ_self T)))
      omega
  have hex : ∃ t, t < p * n + 1 ∧ b (t + 1) = b t := by
    by_contra hcon
    push Not at hcon
    have := hcount (p * n + 1) fun t ht => hcon t ht
    have hle : (b 0).card ≤ p * n := by
      calc (b 0).card ≤ Fintype.card (Fin p × Fin n) := Finset.card_le_univ _
        _ = p * n := by simp
    omega
  obtain ⟨t, htlt, hbt⟩ := hex
  -- `f^[t+1] Ξ₀` is a fixed point
  have hfix : f (f^[t + 1] Ξ₀) = f^[t + 1] Ξ₀ := by
    have := sindyStep_fixed_of_big_eq lam solve (f^[t] Ξ₀) (by
      simpa only [hb, Function.iterate_succ_apply'] using hbt)
    simpa only [Function.iterate_succ_apply'] using this
  have hK' : sindy lam solve K = f^[t + 1] Ξ₀ := by
    have hKt : K = (K - (t + 1)) + (t + 1) := by omega
    show f^[K] Ξ₀ = _
    rw [hKt, Function.iterate_add_apply, Function.iterate_fixed hfix]
  rw [hK']
  exact hfix

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
