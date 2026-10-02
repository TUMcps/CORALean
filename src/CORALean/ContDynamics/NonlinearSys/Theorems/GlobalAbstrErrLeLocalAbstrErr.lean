import CORALean.ContDynamics.NonlinearSys.Operations.GlobalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Operations.LocalAbstrErr
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity

/-!
# Lemma 2: the global abstraction error from the worst local one

[1, Lemma 2]: for a solver "of the form (10)" — one step sharing its
particular-solution term between the error-carrying run `R` and the error-free
run `R̂`, so consecutive global errors grow by at most a fixed per-step factor
`1 + LΔt` before the step's own error is added — the global error after `N`
equal steps of length `Δt` is at most the worst local error over the run,
scaled by a constant depending on `t_end := NΔt` alone.

`hstep` is (10)'s content, cashed out as [1]'s own Appendix-B inequality
`εₖ₊₁ ≤ (1+LΔt)εₖ + εₖ,loc` — mid-proof, right before the paper defers the rest
to a cited textbook's own Grönwall argument. Deriving `hstep` in turn from a
concrete linearization matrix `A`, the Taylor remainder of `e^{AΔt}` and its
Lipschitz constant over `[0,t_end]` is not done here; see the finding on the
paper's page. What *is* proved here, in `aux_gronwall`, is that deferred step:
the discrete Grönwall argument from `hstep` to (30).

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The discrete Grönwall step: a sequence growing by at most a fixed factor
`1 + LΔt` each step, plus a per-step addition bounded by `M`, stays under the
geometric sum that recursion unrolls to. -/
theorem aux_gronwall {L Δt M : ℝ} (hL : 0 < L) (hΔt : 0 < Δt)
    (global loc : ℕ → ℝ) (hzero : global 0 = 0) (N : ℕ)
    (hrec : ∀ k < N, global (k + 1) ≤ (1 + L * Δt) * global k + loc (k + 1))
    (hloc : ∀ k < N, loc (k + 1) ≤ M) :
    global N ≤ M * ((1 + L * Δt) ^ N - 1) / (L * Δt) := by -- --- PROOF ---
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    have ihN : global N ≤ M * ((1 + L * Δt) ^ N - 1) / (L * Δt) :=
      ih (fun k hk => hrec k (hk.trans (Nat.lt_succ_self N)))
        (fun k hk => hloc k (hk.trans (Nat.lt_succ_self N)))
    have hstep : global (N + 1) ≤ (1 + L * Δt) * global N + loc (N + 1) :=
      hrec N (Nat.lt_succ_self N)
    have hlocN : loc (N + 1) ≤ M := hloc N (Nat.lt_succ_self N)
    have hpos : (0:ℝ) ≤ 1 + L * Δt := by positivity
    have hne : L * Δt ≠ 0 := by positivity
    calc global (N + 1) ≤ (1 + L * Δt) * global N + loc (N + 1) := hstep
      _ ≤ (1 + L * Δt) * (M * ((1 + L * Δt) ^ N - 1) / (L * Δt)) + M := by
          have := mul_le_mul_of_nonneg_left ihN hpos
          linarith
      _ = M * ((1 + L * Δt) ^ (N + 1) - 1) / (L * Δt) := by
          field_simp
          ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2]: the global error after `N` equal steps is at most the worst
local error over the run, scaled by a constant depending on `t_end` alone. -/
theorem globalAbstrErr_le_of_localAbstrErr (R Rhat Rabs : ℕ → Set (Vec ℝ n))
    {L Δt tEnd : ℝ} (hL : 0 < L) (hΔt : 0 < Δt) {N : ℕ} (hN : 0 < N)
    (htEnd : (N : ℝ) * Δt = tEnd) (hzero : globalAbstrErr (R 0) (Rhat 0) = 0)
    (hstep : ∀ k < N, globalAbstrErr (R (k + 1)) (Rhat (k + 1)) ≤
      (1 + L * Δt) * globalAbstrErr (R k) (Rhat k) + localAbstrErr (Rabs k)) :
    globalAbstrErr (R N) (Rhat N) ≤ (Real.exp (L * tEnd) - 1) / L / Δt *
      (Finset.range N).sup' (Finset.nonempty_range_iff.mpr hN.ne')
        (fun k => localAbstrErr (Rabs k)) := by -- --- PROOF ---
  set M := (Finset.range N).sup' (Finset.nonempty_range_iff.mpr hN.ne')
    (fun k => localAbstrErr (Rabs k)) with hMdef
  have hmem : ∀ {k : ℕ}, k < N → k ∈ Finset.range N := fun hk => Finset.mem_range.mpr hk
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun k => localAbstrErr (Rabs k)) (hmem hN))
  have hloc : ∀ k < N, localAbstrErr (Rabs k) ≤ M :=
    fun k hk => Finset.le_sup' (fun k => localAbstrErr (Rabs k)) (hmem hk)
  -- (30): unroll the per-step recursion into the geometric closed form
  have hbound : globalAbstrErr (R N) (Rhat N) ≤ M * ((1 + L * Δt) ^ N - 1) / (L * Δt) :=
    aux_gronwall hL hΔt (fun k => globalAbstrErr (R k) (Rhat k))
      (fun j => localAbstrErr (Rabs (j - 1))) hzero N
      (fun k hk => by simpa using hstep k hk) (fun k hk => by simpa using hloc k hk)
  -- `(1+LΔt)^N ≤ e^{LΔt·N} = e^{L·t_end}`, the step [1]'s proof defers
  have hpow : (1 + L * Δt) ^ N ≤ Real.exp (L * Δt) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (L * Δt)]) N
  have hexp : Real.exp (L * Δt) ^ N = Real.exp (L * tEnd) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [← htEnd]; ring
  have hLΔt : (0:ℝ) < L * Δt := by positivity
  calc globalAbstrErr (R N) (Rhat N)
      ≤ M * ((1 + L * Δt) ^ N - 1) / (L * Δt) := hbound
    _ ≤ M * (Real.exp (L * tEnd) - 1) / (L * Δt) := by
        have hnum : M * ((1 + L * Δt) ^ N - 1) ≤ M * (Real.exp (L * tEnd) - 1) :=
          mul_le_mul_of_nonneg_left (by rw [hexp] at hpow; linarith) hM0
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hLΔt))
    _ = (Real.exp (L * tEnd) - 1) / L / Δt * M := by
        field_simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
