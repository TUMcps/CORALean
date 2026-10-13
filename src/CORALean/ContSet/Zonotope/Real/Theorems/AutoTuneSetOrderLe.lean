import CORALean.ContSet.Zonotope.Real.Operations.AutoTuneSetOrder

/-!
# What `Alg. 2` lines 19-22 report is inside the share they searched for

The soundness half of the sweep `ExistsAutoTuneSetOrder` shows non-vacuous: every order
it hands back is one line 22's check cleared, so `Δε^r_k(ρ_k) ≤ ε^{r,τ}_k` holds of the
value returned and not merely of some candidate. That is what line 29's accumulation
`ε^r_{k+1} = ε^r_k + Δε^r_k(ρ_k)` needs to stay inside eq. (35)'s share.

Only the soundness direction of the check is asked, `le a b = true → a ≤ b`: a check that
gives up early reports less often and never lets a wider reduction through.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] lines 19-22: the order the sweep settles on costs a `Δε^r_k(ρ_k)` inside
eq. (35)'s admissible share, that being the check line 22 stops on. -/
theorem Zonotope.autoTuneSetOrder_le {le : ℝ → ℝ → Bool} (hle : ∀ a b : ℝ, le a b = true → a ≤ b)
    (Z : Zonotope (Vec ℝ n)) {εrτ : ℝ} :
    ∀ (k ρ ρ' : ℕ), Zonotope.autoTuneSetOrder le Z εrτ ρ k = some ρ' →
      Z.reduceBoxError ρ' ≤ εrτ := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro ρ ρ' h; rw [Zonotope.autoTuneSetOrder] at h; exact absurd h (by simp)
  | succ k ih =>
    intro ρ ρ' h
    rw [Zonotope.autoTuneSetOrder] at h
    split at h
    -- line 22 cleared this candidate, so the value reported is the one checked
    · rename_i hchk
      rw [Option.some.injEq] at h
      subst h
      exact hle _ _ hchk
    · exact ih _ _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
