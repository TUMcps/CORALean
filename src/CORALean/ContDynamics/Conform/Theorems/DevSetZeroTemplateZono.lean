module

public import CORALean.ContDynamics.Conform.Definitions.DevSet
public import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.SumTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.TemplateZonoAdd

@[expose] public section

/-!
# `R_a(k)` of stretched templates, from an exact initial state

With the initial state known (`X̃₀ = {0}`) and `W`, `V` stretched templates, `R_a(k)` is
the zonotope with center `∑_{i<k} Eᵢ c_W + c_V` [1, Eq. 17] and generators
`[E₀ G'_W ⋯ E_{k-1} G'_W  G'_V]` [1, Eq. 18], `Eᵢ = C Aⁱ`, stretched by `α_W` once per step
and by `α_V`. An equality, as the paper's `=` says.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 17], [1, Eq. 18]: the center and generators of `R_a(k)`. -/
theorem Conform.Plant.devSet_zero_templateZono (sys : Conform.Plant n p q) {ιW ιV : Type}
    [Fintype ιW] [Fintype ιV] (cW : Vec ℝ n) (GW : ιW → Vec ℝ n) (αW : ιW → ℝ) (cV : Vec ℝ q)
    (GV : ιV → Vec ℝ q) (αV : ιV → ℝ) (k : ℕ) :
    sys.devSet {0} (Conform.templateZono cW GW αW) (Conform.templateZono cV GV αV) k
      = Conform.templateZono (∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ cW + cV)
          (Sum.elim (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2) GV)
          (Sum.elim (fun r => αW r.2) αV) := by -- --- PROOF ---
  unfold Conform.Plant.devSet
  simp only [Conform.image_templateZono, Set.image_singleton, mulVec_zero]
  rw [Conform.sum_templateZono, Set.singleton_add]
  simp only [zero_add, Set.image_id']
  rw [Conform.templateZono_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
