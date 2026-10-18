module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptRun

@[expose] public section

/-!
# What one step of `Alg. 2` reports

Three facts about a step [1, Alg. 2] completes, one per tuned quantity it hands
on. The horizon is line 1's update of the last one. The time advances by a step
size that is that horizon scaled down by `ζ_δ` a whole number of times, which
is eq. (58)'s shape and is what makes `Δt* ≤ h_k` for `ζ_δ ∈ (0,1)`. And the
abstraction order stays in `{1,2}`, §5.2's restriction for a linearization
approach, which line 13 is asked to respect and does.

Nothing here is about the sets: what `optDeltat` and `estimateGain` guarantee
is proved where they are defined, and the enclosure the step computes needs the
certificate lines 4-5 do not carry — `abstrErrLoop_subset` is the part of that
this tree can state.

A step that gave out reports nothing, so the statement is about `some s'` only,
as the budget theorems of the CDC paper's `Alg. 2` are.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Eq. (47) chooses between two orders, and eq. (46) may keep the one in hand:
those are the only three values line 13 can report. -/
theorem aux_tuneAbstrOrder_mem (le : ℝ → ℝ → Bool) (ζK φstar rabs rabsLast : ℝ)
    (d1 d2 : Fin n → ℝ) {κ : ℕ} (hκ : κ = 1 ∨ κ = 2) :
    tuneAbstrOrder le ζK φstar rabs rabsLast d1 d2 κ = 1 ∨
      tuneAbstrOrder le ζK φstar rabs rabsLast d1 d2 κ = 2 := by -- --- PROOF ---
  rw [tuneAbstrOrder]
  split
  · exact hκ
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: the horizon is line 1's, the step taken is that horizon scaled
by `ζ_δ` a whole number of times, and the order stays in `{1,2}`. -/
theorem NonlinearSys.adaptStep_invariant (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK : ℝ) (ηlin ηabs o fuel : ℕ)
    {s s' : NonlinearSys.AdaptState S n}
    (h : sys.adaptStep U lin Φ sub enlarge le rad dbox ζδ ζh ζZ ζK ηlin ηabs o fuel s
      = some s') : -- --- STMT ---
    s'.h = s.h * (ζδ - ζh) / (ζδ - s.φ) ∧ (∃ j : ℕ, s'.t = s.t + s'.h * ζδ ^ j) ∧
      ((s.κ = 1 ∨ s.κ = 2) → (s'.κ = 1 ∨ s'.κ = 2)) := by -- --- PROOF ---
  simp only [NonlinearSys.adaptStep] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    -- both orders' error loops returned, so the step reports
    · rw [Option.some.injEq] at h
      subst h
      exact ⟨rfl, ⟨_, rfl⟩, fun hκ => aux_tuneAbstrOrder_mem _ _ _ _ _ _ _ hκ⟩
    · exact absurd h (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
