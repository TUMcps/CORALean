module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop

@[expose] public section

/-!
# What the abstraction error's loop reports is conservative

The soundness of lines 8-11 of [1, Alg. 1], which are lines 7-10 of [2, Alg. 1]:
an error the loop reports was computed from an applied error that contains it.
That is line 11's exit condition read as sets, and it is what makes line 12's `abstrSol` an
over-approximation — the sets `abstrErr` was evaluated against were at least as
large as the error they turned out to induce.

One hypothesis, on the caller's check: `sub a b = true` implies
`construct a ⊆ construct b`. Nothing asks the converse, so a test that gives up
early loses iterations and never reports a wrong error, which is why the loop
returns an `Option` rather than a value with a junk branch.

The induction is on the loop's own fuel and the invariant is carried by the
check alone; nothing here needs the loop to terminate.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] lines 8-11: the reported error is `abstrErr` of an applied
error that contains it. -/
theorem abstrErrLoop_subset {sub : S n → S n → Bool}
    (hsub : ∀ a b : S n, sub a b = true → construct a ⊆ construct b)
    (enlarge Φ : S n → S n) : -- --- CONCL ---
    ∀ (fuel : ℕ) (Ψ Ψ' : S n), abstrErrLoop sub enlarge Φ Ψ fuel = some Ψ' →
      ∃ Ψapp, Ψ' = Φ Ψapp ∧ construct Ψ' ⊆ construct Ψapp := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro Ψ Ψ' h; rw [abstrErrLoop] at h; exact absurd h (by simp)
  | succ k ih =>
    intro Ψ Ψ' h
    simp only [abstrErrLoop] at h
    split at h
    -- the test cleared, so the enlarged error is the one it was cleared against
    · rename_i hc
      rw [Option.some.injEq] at h
      subst h
      exact ⟨enlarge Ψ, rfl, hsub _ _ hc⟩
    · exact ih _ _ h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
