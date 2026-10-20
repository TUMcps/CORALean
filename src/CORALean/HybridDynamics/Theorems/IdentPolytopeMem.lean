module

public import CORALean.HybridDynamics.Definitions.IdentHA

@[expose] public section

/-!
# Membership in the polytope `⟨C, d⟩_P`

A point is in the H-polytope `IdentHA.polytope cs` of the rows `cs` exactly when it satisfies
every inequality `cᵢᵀx ≤ dᵢ` ([1, Def. 2]).

## Inputs
* `cs` – polytope rows
* `x` – point

## Hypotheses
* none

## Conclusion
* the point lies in the polytope iff it satisfies every row

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x` is in the H-polytope of the rows `cs` iff `cᵀx ≤ d` for every row `(c, d)` of `cs`. -/
theorem IdentHA.mem_polytope_construct_iff (cs : List (Vec ℝ n × ℝ)) (x : Vec ℝ n) :
    x ∈ (IdentHA.polytope cs).construct ↔ ∀ p ∈ cs, p.1 ⬝ᵥ x ≤ p.2 := by -- --- PROOF ---
  constructor
  · rintro ⟨h, -⟩ p hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
    exact h i
  · intro h
    exact ⟨fun i => h _ (List.get_mem cs i), fun i => i.elim0⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
