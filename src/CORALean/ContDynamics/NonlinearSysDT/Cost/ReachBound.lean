import CORALean.ContDynamics.LinearSysDT.Cost.ReachBound
import CORALean.ContDynamics.NonlinearSysDT.Cost.Reach

/-!
# `reach` costs at most `k` worst-case linear steps

The second worked composition, and it composes one level higher than the first:
`LinearSysDT.reachCost_le` is used whole, at `k = 1`, rather than the leaf
counts under it. Nothing is asserted here either.

Two hypotheses is all it takes beyond that. `hR₀` is the one the size facts
cannot supply, exactly as in the linear file. `hL` is new and is what
re-linearization costs the statement: each step gets its *own* input set, built
by `linInput` from that step's abstraction error, and a run has no bound on
those unless the caller gives one. A caller whose errors are uniform passes the
same `hU` every step and gets the linear bound back unchanged.

The bound is the linear one, `LinearSysDT.reachStepBound`, not a fresh number:
the operations a step runs are the same operations, so the count is the same
count and the re-linearization is free in it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every set the run holds is at order `o`: one linear step ends in a
`reduce`, and the caller's hypothesis covers the set before the first. -/
theorem NonlinearSysDT.aux_reach_h_le (sys : NonlinearSysDT n m) {U : Zonotope (Vec ℝ m)}
    {o : ℕ} (ho : 0 < o) (steps : ℕ → sys.LinStep (S := 𝒵) U) (R₀ : Zonotope (Vec ℝ n))
    (hR₀ : R₀.h ≤ o * n) : ∀ k, (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps).h ≤ o * n
  | 0 => hR₀
  | _ + 1 => LinearSysDT.reach_order_le _ ho _ _ 0

/-- The linear step bound is monotone in the input set's generator count, which
is what lets one `hU` stand for every step's own input set. -/
theorem NonlinearSysDT.aux_stepBound_mono (n o : ℕ) {hU hU' : ℕ} (h : hU ≤ hU') :
    LinearSysDT.reachStepBound n hU o ≤ LinearSysDT.reachStepBound n hU' o :=
  Cost.add_le_add le_rfl (Zonotope.reduceGirardCost_mono n (Nat.add_le_add_left h _))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` re-linearized steps cost at most `k` worst-case linear steps. Nothing
asserted here: it is `LinearSysDT.reachCost_le` at one step, `k` times. -/
theorem NonlinearSysDT.reachCost_le (sys : NonlinearSysDT n m) {U : Zonotope (Vec ℝ m)}
    {o : ℕ} (ho : 0 < o) (steps : ℕ → sys.LinStep (S := 𝒵) U) (R₀ : Zonotope (Vec ℝ n))
    (hU : ℕ) (hR₀ : R₀.h ≤ o * n) (hL : ∀ j, ((steps j).linInput).h ≤ hU) (k : ℕ) :
    sys.reachCost o ho steps R₀ k ≤ k • LinearSysDT.reachStepBound n hU o := by -- --- PROOF ---
  induction k with
  | zero => simp [NonlinearSysDT.reachCost]
  | succ k ih =>
    -- one linear step, at the set reached so far and at this step's own input
    have h1 := (NonlinearSysDT.linearize (steps k).A).reachCost_le ho
      (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) (steps k).linInput
      (sys.aux_reach_h_le ho steps R₀ hR₀ k) 1
    have h2 := NonlinearSysDT.aux_stepBound_mono n o (hL k)
    -- and that step's own input is within the uniform bound the caller gave
    have hstep : (NonlinearSysDT.linearize (steps k).A).reachCost o ho
        (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) (steps k).linInput 1
          ≤ LinearSysDT.reachStepBound n hU o := le_trans h1 (by simpa using h2)
    have h := Nat.add_le_add (Cost.le_iff.mp ih) (Cost.le_iff.mp hstep)
    refine Cost.le_iff.mpr ?_
    simpa [NonlinearSysDT.reachCost, Nat.succ_mul] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
