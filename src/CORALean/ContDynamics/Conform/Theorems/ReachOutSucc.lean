import CORALean.ContDynamics.Conform.Definitions.ReachOut
import Mathlib.Logic.Function.Basic

/-!
# [1, Eq. 6]: one step of the reachable set

`R(k+1) = C (A X(k) ⊕ B u(k) ⊕ W) ⊕ D u(k+1) ⊕ V`, `X(k)` the reachable states — an
equality, the set-based evaluation of [1, Eq. 5] losing nothing: each step draws a
fresh disturbance, independent of those before it.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state at `k` reads only the disturbances before `k`. -/
theorem aux_state_congr (sys : Conform.Plant n p q) (x0 : Vec ℝ n) (u : ℕ → Vec ℝ p)
    {w w' : ℕ → Vec ℝ n} : ∀ k, (∀ i < k, w i = w' i) →
      sys.state x0 u w k = sys.state x0 u w' k := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [Conform.Plant.state]
    rw [ih fun i hi => h i (by omega), h k (by omega)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6]: the reachable outputs one step on, from the reachable states. -/
theorem Conform.Plant.reachOut_succ (sys : Conform.Plant n p q) (X0 : Set (Vec ℝ n))
    (u : ℕ → Vec ℝ p) (W : Set (Vec ℝ n)) (V : Set (Vec ℝ q)) (k : ℕ) :
    sys.reachOut X0 u W V (k + 1)
      = (fun x => sys.C *ᵥ x) '' ((fun x => sys.A *ᵥ x) '' sys.reachState X0 u W k
          + {sys.B *ᵥ u k} + W) + {sys.D *ᵥ u (k + 1)} + V := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x0, hx0, w, hw, v, hv, rfl⟩
    refine Set.add_mem_add (Set.add_mem_add ⟨_, Set.add_mem_add (Set.add_mem_add
      ⟨_, ⟨x0, hx0, w, fun i hi => hw i (by omega), rfl⟩, rfl⟩ rfl) (hw k (by omega)), rfl⟩
      rfl) hv
  · rintro ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨s, ⟨x0, hx0, w', hw', rfl⟩, rfl⟩, _, rfl, rfl⟩, w0, hw0, rfl⟩,
      rfl⟩, _, rfl, rfl⟩, v, hv, rfl⟩
    -- the fresh disturbance is placed at step `k`, after every one the state read
    refine ⟨x0, hx0, Function.update w' k w0, fun i hi => ?_, v, hv, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hw' i hlt
      · rw [Function.update_self]
        exact hw0
    · have hs : sys.state x0 u (Function.update w' k w0) k = sys.state x0 u w' k :=
        aux_state_congr sys x0 u k fun i hi => Function.update_of_ne (by omega) _ _
      simp only [Conform.Plant.output, Conform.Plant.state, hs, Function.update_self,
        mulVec_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
