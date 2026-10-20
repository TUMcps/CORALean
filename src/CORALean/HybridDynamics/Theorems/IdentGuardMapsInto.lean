module

public import CORALean.HybridDynamics.Operations.IdentGuard
public import CORALean.HybridDynamics.Theorems.IdentPolytopeMem
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The guard of Prop. 1 maps every state entering it into the target invariant

[1, Prop. 1]: for the surface `H = ⟨a, b, [], []⟩_H`, the reset `r(x) = H x + k` and the target
invariant `Y = ⟨C, d⟩_P`, the guard `G = ⟨a, b, C H, d - C k⟩_H` guarantees that all states
entering it are mapped into `Y`. `Y` is the H-polytope of the rows `(cᵢ, dᵢ)`, `G` the
constrained hyperplane `IdentHA.conHyperplane` of the rows `identGuard` builds. That `G` is
exactly the states of `H` mapped into `Y` is `conHyperplane_identGuard`.

## Inputs
* `a` – hyperplane normal
* `b` – hyperplane offset
* `H` – reset matrix
* `k` – reset offset
* `cs` – invariant rows

## Hypotheses
* none

## Conclusion
* every state of the guard is reset into the invariant

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: every state `x` of the guard `G = ⟨a, b, C H, d - C k⟩_H` is mapped by the
reset `r(x) = H x + k` into the polytope `Y = ⟨C, d⟩_P`. -/
theorem IdentHA.identGuard_maps_into (a : Vec ℝ n) (b : ℝ) (H : Mat ℝ n n) (k : Vec ℝ n)
    (cs : List (Vec ℝ n × ℝ)) : -- --- CONCL ---
    ∀ x ∈ IdentHA.conHyperplane a b (IdentHA.identGuard H k cs),
      H *ᵥ x + k ∈ (IdentHA.polytope cs).construct := by -- --- PROOF ---
  rintro x ⟨-, hx⟩
  rw [IdentHA.mem_polytope_construct_iff] at hx ⊢
  intro q hq
  have h : (Hᵀ *ᵥ q.1) ⬝ᵥ x ≤ q.2 - q.1 ⬝ᵥ k := hx _ (List.mem_map_of_mem hq)
  have hid : q.1 ⬝ᵥ (H *ᵥ x + k) = (Hᵀ *ᵥ q.1) ⬝ᵥ x + q.1 ⬝ᵥ k := by
    rw [dotProduct_add, dotProduct_mulVec, mulVec_transpose]
  rw [hid]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
