import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch

/-!
# What a successful search hands back

`abstrErrPolySearch`'s `some` read back: the linearization it was handed, the region
and the error of one candidate `k`, and the *polynomial* certificate at that
candidate — stronger than the `AbstractionError` the `LinStep` carries, which has
forgotten which factors carry the error.

No bound on `k` is stated. The search tries candidates `0` to `fuel - 1`, but the
recursion that does so is its file's own, and nothing downstream needs the index,
only that the step is one of the candidates and that the certificate held there.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `some` from the search is candidate `k`'s region and error at the linearization
it was handed, with the polynomial certificate holding at `k`. -/
theorem NonlinearSys.abstrErrPolySearch_eq_some {sys : NonlinearSys n m}
    {U : PolyZonotope (Vec ℝ m)} {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {pZ : ℕ → PolyZonotope (Vec ℝ n)} {Ba : ∀ k, Set (Fin (pZ k).p → ℝ)}
    {L : ℕ → PolyZonotope (Vec ℝ n)} {hp : ∀ k, (L k).p = (pZ k).p}
    {hBa : ∀ k, ∀ a ∈ Ba k, ∀ j, |a j| ≤ 1} {Ws : ℕ → PolyZonotope (Vec ℝ n)} {fuel : ℕ}
    {step : sys.LinStep (S := 𝒫𝒵) U}
    (h : sys.abstrErrPolySearch U A B xs us pZ Ba L hp hBa Ws fuel = some step) :
    ∃ k, PolyAbstractionError sys.f A B xs us (pZ k) (Ba k) (construct U) (L k) (hp k) (Ws k) ∧
      step.A = A ∧ step.B = B ∧ step.xs = xs ∧ step.us = us ∧
      step.R = (pZ k).subsetAt (Ba k) ∧ step.L = L k ⊞ Ws k := by
  unfold NonlinearSys.abstrErrPolySearch at h
  -- the search's `some` is a certified index, and the step is built from it alone
  obtain ⟨⟨k, hk⟩, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨k, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
