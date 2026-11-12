module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedErrorLeWeighted

@[expose] public section

/-!
# The error inside a restart window, with the exact steps measured in a Lyapunov weight

[1, Sec. 7] at every time of a window, not only at its end. After `N` windows the accumulated
error has weight-gauge at most `β_N` (`Krylov.restarted_error_le_weighted`); inside window `N`,
at time `s ∈ [0, T]`, the exact trajectory is `e^{sA} v^{[N]}` and the approximate one `W(s)`, with
the local error `‖e^{sA} w^{[N]} - W(s)‖₂ ≤ ε_N` at every such `s`. For a weight with a rate
`μ ≤ 0` the exact flow does not grow the gauge (`e^{μs} ≤ 1`), so the error at `s` is at most
`(β_N + √b ε_N)/√a`: the decay of `β_N` inside the window is not counted, which is what CORA.cpp's
`RestartedBound::window_bound` computes. The proof appends the time `s` as one more window of
length `s` to the recursion of `Krylov.restarted_error_le_weighted`.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `μ` – growth rate in the weight
* `a` – lower bound of the weight's quadratic form
* `b` – upper bound of the weight's quadratic form
* `N` – number of finished windows
* `Δt` – lengths of the finished windows
* `T` – length of window `N`
* `v` – exact iterates
* `w` – approximate iterates
* `S` – approximate step maps of the finished windows
* `W` – approximate trajectory inside window `N`, from `w^{[N]}`
* `ε` – local 2-norm errors
* `β` – bound of the accumulated error in the weight

## Hypotheses
* `hS` – weight symmetric
* `hPA` – `x*PAx ≤ μ x*Px`
* `ha` – `a x*x ≤ x*Px`
* `hb` – `x*Px ≤ b x*x`
* `ha0` – `a` positive
* `hμ` – the rate is nonpositive
* `hΔt` – lengths of the finished windows nonnegative
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors of the finished windows within `ε_j`
* `hβ0` – bound nonnegative at the start
* `hβ` – bound follows the recursion `e^{μΔt_j} β_j + √b ε_j ≤ β_{j+1}`
* `hβN` – bound nonnegative at window `N`
* `hin` – local error of window `N` within `ε_N` at every time of it

## Conclusion
* the 2-norm error at every time `s ∈ [0, T]` of window `N` is at most `(β_N + √b ε_N)/√a`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the hypotheses of `Krylov.restarted_error_le_weighted` for `N` windows, a rate `μ ≤ 0`,
`0 ≤ β_N` and `‖e^{sA} w^{[N]} - W(s)‖₂ ≤ ε_N` for `0 ≤ s ≤ T`: `‖e^{sA} v^{[N]} - W(s)‖₂ ≤
(β_N + √b ε_N)/√a` for `0 ≤ s ≤ T`. -/
theorem Krylov.restarted_error_le_weighted_inside (A P : Mat ℝ n n) (μ a b : ℝ) (hS : Pᵀ = P)
    (hPA : ∀ x, x ⬝ᵥ (P *ᵥ (A *ᵥ x)) ≤ μ * (x ⬝ᵥ (P *ᵥ x)))
    (ha : ∀ x, a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) (hb : ∀ x, x ⬝ᵥ (P *ᵥ x) ≤ b * (x ⬝ᵥ x))
    (ha0 : 0 < a) (hμ : μ ≤ 0) (N : ℕ) (Δt : ℕ → ℝ) (T : ℝ) (hΔt : ∀ j < N, 0 ≤ Δt j)
    (v w : ℕ → Vec ℝ n) (S : ℕ → Vec ℝ n → Vec ℝ n) (W : ℝ → Vec ℝ n) (ε β : ℕ → ℝ)
    (hv : ∀ j < N, v (j + 1) = exp (Δt j • A) *ᵥ v j) (hw : ∀ j < N, w (j + 1) = S j (w j))
    (h0 : v 0 = w 0) (hloc : ∀ j < N, ‖exp (Δt j • A) *ᵥ w j - S j (w j)‖₂ ≤ ε j)
    (hβ0 : 0 ≤ β 0)
    (hβ : ∀ j < N, Real.exp (μ * Δt j) * β j + Real.sqrt b * ε j ≤ β (j + 1))
    (hβN : 0 ≤ β N)
    (hin : ∀ s, 0 ≤ s → s ≤ T → ‖exp (s • A) *ᵥ w N - W s‖₂ ≤ ε N) : -- --- CONCL ---
    ∀ s, 0 ≤ s → s ≤ T →
      ‖exp (s • A) *ᵥ v N - W s‖₂ ≤ (β N + Real.sqrt b * ε N) / Real.sqrt a := by -- --- PROOF ---
  intro s hs0 hsT
  have hε : 0 ≤ ε N := (norm₂_nonneg _).trans (hin s hs0 hsT)
  -- window `N` is appended as one more window of length `s`
  have hmain := Krylov.restarted_error_le_weighted A P μ a b hS hPA ha hb ha0 (N + 1)
    (fun j => if j < N then Δt j else s)
    (fun j hj => by
      by_cases h : j < N
      · simpa [h] using hΔt j h
      · simpa [h] using hs0)
    (fun j => if j ≤ N then v j else exp (s • A) *ᵥ v N)
    (fun j => if j ≤ N then w j else W s)
    (fun j => if j < N then S j else fun _ => W s)
    (fun j => if j < N then ε j else ε N)
    (fun j => if j ≤ N then β j else β N + Real.sqrt b * ε N)
    -- the exact and the approximate iterates continue by the finished windows, then by `s`
    (fun j hj => by
      by_cases h : j < N
      · have h' : j + 1 ≤ N := h
        have h'' : j ≤ N := h.le
        simpa [h, h', h''] using hv j h
      · have hjN : j = N := by omega
        subst hjN
        simp)
    (fun j hj => by
      by_cases h : j < N
      · have h' : j + 1 ≤ N := h
        have h'' : j ≤ N := h.le
        simpa [h, h', h''] using hw j h
      · have hjN : j = N := by omega
        subst hjN
        simp)
    -- same start, local errors of the finished windows and of the appended one
    (by simpa [Nat.zero_le] using h0)
    (fun j hj => by
      by_cases h : j < N
      · have h' : j ≤ N := h.le
        simpa [h, h'] using hloc j h
      · have hjN : j = N := by omega
        subst hjN
        simpa using hin s hs0 hsT)
    -- the bound: `β_j` for the finished windows, `β_N + √b ε_N` for the appended one
    (by simpa using hβ0)
    (fun j hj => by
      by_cases h : j < N
      · have h' : j + 1 ≤ N := h
        have h'' : j ≤ N := h.le
        simpa [h, h', h''] using hβ j h
      · have hjN : j = N := by omega
        subst hjN
        -- the decay of `β_N` is not counted
        have hexp : Real.exp (μ * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have := mul_le_mul_of_nonneg_right hexp hβN
        simp only [lt_irrefl, if_false, le_refl, if_true, Nat.not_succ_le_self]
        linarith)
  simpa using hmain

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
