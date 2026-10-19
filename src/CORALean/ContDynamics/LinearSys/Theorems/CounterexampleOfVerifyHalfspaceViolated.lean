module

public import CORALean.ContDynamics.LinearSys.Theorems.SupportCounterexampleViolates
public import CORALean.Specification.Theorems.ExistsRoundOfVerifyHalfspaceEqViolated

@[expose] public section

/-!
# `[1, Alg. 2]`'s `unsafe` comes with a run that leaves the safe set

`verifyHalfspace` run on the lower bounds of [1, Alg. 1 (lower bounds)] — line 16's
`ρ(Ř(τ_k), H_(i,·)ᵀ)` at the step `Δt = t_end / 2^r` of round `r` — answers
`violated` only from a round, step and row whose lower bound crossed `f_(i)`
(`exists_round_of_verifyHalfspace_eq_violated`). There the counterexample of
[1]'s Sec. 5.1, `supportCounterexample` at `t_k` or `t_{k+1}`, is a `IsTrajectory` of
the system on the whole horizon `[0, t_end]` (`isTrajectory_heldInput`) whose state
at that time violates row `i` of the safe set (`supportCounterexample_violates`).

So the answer is not only sound, as `not_holds_safeSet_of_verifyHalfspace_violated`
says of any witnesses, but constructive: the falsifying initial state and
piecewise-constant input are named.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: an `unsafe` answer on [1, Alg. 1 (lower bounds)]'s bounds names a round `r'`, a
row `i` and a step `j`, and the counterexample run there is a `IsTrajectory` on `[0, t_end]` whose
state at `t_j ∈ [0, t_end]` violates `H_(i,·) x ≤ f_(i)`. -/
theorem LinearSys.counterexample_of_verifyHalfspace_violated (sys : LinearSys 𝕋 n)
    (R₀ U : S n) (hU : Bornology.IsBounded (construct U)) {tEnd : ℝ} (htEnd : 0 < tEnd)
    {ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct R₀)
    (hνU : ∀ d, νU d ∈ construct U) {c : Vec ℝ n}
    (hc : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d c ≤ d (νU d)) {ι : Type} (H : ι → Vec ℝ n →ₗ[ℝ] ℝ)
    (f : ι → ℝ) {bndUp : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {r fuel : ℕ}
    (h : verifyHalfspace bndUp
      (fun r k i => (sys.supportLower (tEnd / 2 ^ r) ν₀ νU c (H i) (k + 1)).ρRτ) f r fuel
        = .violated) : -- --- CONCL ---
    ∃ (r' j : ℕ) (i : ι), (j : ℝ) * (tEnd / 2 ^ r') ∈ Set.Icc 0 tEnd ∧
      sys.IsCanonicalTrajectory (Set.Icc 0 tEnd) R₀ U
        (sys.closedForm (sys.supportCounterexample (tEnd / 2 ^ r') ν₀ νU (H i) j).1
          (LinearSys.heldInput (tEnd / 2 ^ r')
            (sys.supportCounterexample (tEnd / 2 ^ r') ν₀ νU (H i) j).2))
        (LinearSys.heldInput (tEnd / 2 ^ r')
          (sys.supportCounterexample (tEnd / 2 ^ r') ν₀ νU (H i) j).2) ∧
      f i < H i (sys.closedForm (sys.supportCounterexample (tEnd / 2 ^ r') ν₀ νU (H i) j).1
        (LinearSys.heldInput (tEnd / 2 ^ r')
          (sys.supportCounterexample (tEnd / 2 ^ r') ν₀ νU (H i) j).2)
        (j * (tEnd / 2 ^ r'))) := by -- --- PROOF ---
  obtain ⟨r', _, k, i, hlt⟩ := exists_round_of_verifyHalfspace_eq_violated h
  have hpow : (0:ℝ) < 2 ^ r' := pow_pos two_pos r'
  have hΔt : 0 < tEnd / 2 ^ r' := div_pos htEnd hpow
  obtain ⟨j, hj, -, hviol⟩ :=
    sys.supportCounterexample_violates R₀ U hU hΔt hν₀ hνU hc (H i) hlt
  -- `t_j ≤ t_{k+1} ≤ t_end`, as `k` is one of round `r'`'s `2^{r'}` steps
  have hjle : (j : ℝ) ≤ 2 ^ r' := by
    have hk := k.isLt
    have : j ≤ 2 ^ r' := by omega
    exact_mod_cast this
  refine ⟨r', j, i, ⟨mul_nonneg j.cast_nonneg hΔt.le, ?_⟩,
    sys.isTrajectory_heldInput R₀ U hU htEnd.le _ (hν₀ _) (fun _ => hνU _), hviol⟩
  calc (j : ℝ) * (tEnd / 2 ^ r') ≤ 2 ^ r' * (tEnd / 2 ^ r') :=
        mul_le_mul_of_nonneg_right hjle hΔt.le
    _ = tEnd := mul_div_cancel₀ tEnd hpow.ne'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
