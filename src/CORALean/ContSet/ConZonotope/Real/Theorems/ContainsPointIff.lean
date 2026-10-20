module

public import CORALean.ContSet.ConZonotope.Real.Operations.ContainsPoint
public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff

@[expose] public section

/-!
# A constrained zonotope contains a point iff the stacked zonotope contains the stacked point

CORA's `aux_containsPoint` for `'exact'`: `p ∈ {c + G β : |β| ≤ 1, A β = b}` exactly when
`[p; b] ∈ zonotope([c; 0], [G; A])`. The upper block of the stacked system is the generator
equation `p = c + G β`, the lower block the constraint `A β = b`, with the same `β`.

## Inputs
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `p` – point to test

## Hypotheses
* none

## Conclusion
* containment holds iff the stacked zonotope contains the stacked point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.containsPoint_iff (c : Vec ℝ n) (G : Fin h → Vec ℝ n) (A : Mat ℝ q h)
    (b : Vec ℝ q) (p : Vec ℝ n) :
    ConZonotope.containsPoint c G A b p ↔
      p ∈ (ConZonotope.ofMat c G A b).construct := by -- --- PROOF ---
  rw [ConZonotope.mem_ofMat_iff]
  constructor
  · -- a stacked coefficient vector gives both blocks: the generators and the constraint rows
    rintro ⟨β, hβ, hx⟩
    refine ⟨β, hβ, fun i => ?_, ?_⟩
    · have := congrFun (congrArg Prod.snd hx) i
      simp [ConZonotope.stack, Prod.snd_sum, Matrix.mulVec, dotProduct,
        Finset.sum_apply, mul_comm] at this ⊢
      exact this.symm
    · have := congrArg Prod.fst hx
      simp [ConZonotope.stack, Prod.fst_sum] at this ⊢
      exact this
  · -- and the two blocks together are the stacked point
    rintro ⟨β, hβ, hA, hx⟩
    refine ⟨β, hβ, Prod.ext ?_ ?_⟩
    · simp [ConZonotope.stack, Prod.fst_sum] at hx ⊢
      exact hx
    · funext i
      have := hA i
      simp [ConZonotope.stack, Prod.snd_sum, Matrix.mulVec, dotProduct,
        Finset.sum_apply, mul_comm] at this ⊢
      exact this.symm


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
