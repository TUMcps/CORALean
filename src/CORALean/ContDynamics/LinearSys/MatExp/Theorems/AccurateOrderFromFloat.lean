import CORALean.ContDynamics.LinearSys.MatExp.Operations.AccurateOrderFromFloat

/-!
# What an order `accurateOrderFrom` returns passed

By induction on the fuel, with the carried values pinned to the power, the
factorial and the count they stand for: each is advanced by the step of its own
recursion, so the tests the loop accepted at are `le nrm (half (nsmulDown (η + 2)
one))` and `le (expRemainderBound nrm η) tol` themselves, at an order no lower
than where it started.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.accurateOrderFrom_spec {nrm tol : 𝕋} :
    ∀ {fuel η η' : ℕ} {p f c : 𝕋}, p = MatExp.powUp (η + 1) nrm →
      f = MatExp.factorialDown (η + 1) → c = nsmulDown (η + 2) one →
      MatExp.accurateOrderFrom nrm tol fuel η p f c = some η' →
      le nrm (half (nsmulDown (η' + 2) (one : 𝕋))) = true ∧ η ≤ η'
        ∧ le (MatExp.expRemainderBound nrm η') tol = true := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro η η' p f c _ _ _ h; simp [MatExp.accurateOrderFrom] at h
  | succ fuel ih =>
    intro η η' p f c hp hf hc h
    rw [MatExp.accurateOrderFrom] at h
    split_ifs at h with htest
    · -- accepted here: the test is the two comparisons at `η` itself
      cases h
      rw [Bool.and_eq_true] at htest
      subst hp hf hc
      exact ⟨htest.1, le_rfl, htest.2⟩
    · -- rejected: the carried values advance to `η + 1` by their own recursions
      obtain ⟨h1, h2, h3⟩ := ih (η := η + 1) (by rw [hp]; rfl) (by rw [hf, hc]; rfl)
        (by rw [hc]; rfl) h
      exact ⟨h1, by omega, h3⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
