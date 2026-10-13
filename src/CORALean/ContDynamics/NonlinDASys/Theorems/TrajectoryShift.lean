module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# A run of the DAE, restarted at a later time

A run of the DAE on `[0, T]` is, from `a` on, a run on `[0, b]` for `a + b ≤ T` once time is
counted from `a`, started in any set that holds `x(a)`. What `[1, Alg. 1]` does at each step:
the set `Rᵈ(t_k)` is the new initial set, and the step's soundness is about the run from `t_k`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run from `a` on, with time counted from `a`, is a run on `[0, b]` from any set holding
`x(a)`. -/
theorem NonlinDASys.Trajectory.shift {sys : NonlinDASys n p m} {T : ℝ} {R₀ : Zonotope (Vec ℝ n)}
    {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory (S := 𝒵) (Set.Icc 0 T) R₀ U x y u) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a + b ≤ T) {Z : Zonotope (Vec ℝ n)} (hx : x a ∈ Z.construct) :
    sys.Trajectory (S := 𝒵) (Set.Icc 0 b) Z U (fun s => x (a + s)) (fun s => y (a + s))
      (fun s => u (a + s)) where
  init := by
    show x (a + 0) ∈ Z.construct
    rw [add_zero]
    exact hx
  input s hs := traj.input (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  flow s hs := by
    have hmem : a + s ∈ Set.Icc 0 T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : HasDerivWithinAt (fun s => a + s) 1 (Set.Icc 0 b) s :=
      HasDerivWithinAt.const_add a (hasDerivWithinAt_id s _)
    have h3 := (traj.flow (a + s) hmem).scomp s h2 (fun s' hs' =>
      ⟨by linarith [hs'.1], by linarith [hs'.2]⟩)
    exact h3.congr_deriv (by simp)
  constraint s hs := traj.constraint (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
