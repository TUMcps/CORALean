module

public import CORALean.ContDynamics.Conform.Definitions.ReachOut
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# [1, Eq. 7] as printed is not the reachable set

[1, Eq. 7] unrolls [1, Eq. 6] to `R(k+1) = C(A^{k+1} X(0) ⊕ ∑_{i=0}^k Aⁱ B u(i) ⊕ ⨁_{i=0}^k Aⁱ W)
⊕ D u(k+1) ⊕ V`. The input term has its powers reversed: `u(i)` enters `x(k+1)` through
`A^{k-i} B`, not `Aⁱ B`. At `A = 2`, `B = C = 1`, `D = 0`, `X(0) = W = V = {0}` and the
inputs `u(0) = 1`, `u(1) = 0`, the run reaches `y(2) = A B u(0) = 2`, while the printed
set is `{B u(0) + A B u(1)} = {1}`. The disturbance term is unaffected — `W` is the same
at every step, so `⨁ A^{k-i} W = ⨁ Aⁱ W` — and so is everything the paper derives from
(7), [1, Eq. 15] subtracting the input term whatever its form: with `A^{k-i}`, (7) is
`mem_reachOut_iff` at `x0 = 0`, the image under `C` distributed over the sum.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7] as printed differs from the reachable set at `k + 1 = 2`. -/
theorem Conform.Plant.reachOut_ne_printed : -- --- STMT ---
    ∃ (sys : Conform.Plant 1 1 1) (u : ℕ → Vec ℝ 1),
      sys.reachOut {0} u {0} {0} 2 ≠
        (fun x => sys.C *ᵥ x) '' ((fun x => (sys.A ^ 2) *ᵥ x) '' {0}
          + {∑ i : Fin 2, (sys.A ^ (i : ℕ) * sys.B) *ᵥ u i}
          + ∑ i : Fin 2, (fun x => (sys.A ^ (i : ℕ)) *ᵥ x) '' {0})
        + {sys.D *ᵥ u 2} + {0} := by -- --- PROOF ---
  refine ⟨⟨!![2], !![1], !![1], !![0]⟩, fun i => if i = 0 then ![1] else 0, fun h => ?_⟩
  -- the run from `0` with no disturbance reaches `2`
  have hmem : (![2] : Vec ℝ 1) ∈ Conform.Plant.reachOut ⟨!![2], !![1], !![1], !![0]⟩ {0}
      (fun i => if i = 0 then ![1] else 0) {0} {0} 2 := by
    refine ⟨0, rfl, 0, fun i _ => rfl, 0, rfl, ?_⟩
    funext j
    fin_cases j
    simp [Conform.Plant.output, Conform.Plant.state, dotProduct]
  rw [h] at hmem
  -- every point of the printed set is `1`
  obtain ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨a0, ha0, rfl⟩, s, hs, rfl⟩, b, hb, rfl⟩, rfl⟩, d, hd, rfl⟩,
    v, hv, hy⟩ := hmem
  rw [Set.mem_singleton_iff] at ha0 hs hd hv
  obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).mp hb
  have hg0 : ∀ i, g i = 0 := fun i => by
    obtain ⟨z, hz, hgz⟩ := hg i
    rw [Set.mem_singleton_iff] at hz
    rw [← hgz, hz]
    exact mulVec_zero _
  subst ha0 hs hd hv
  have h0 := congrFun hy 0
  simp [hg0, Fin.sum_univ_two, dotProduct] at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
