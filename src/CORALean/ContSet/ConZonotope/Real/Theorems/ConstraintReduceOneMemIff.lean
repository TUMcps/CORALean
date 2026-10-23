module

public import CORALean.ContSet.ConZonotope.Real.Operations.ConstraintReduce
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff

@[expose] public section

/-!
# `ConZonotope.constraintReduce` at `Λ_A = I`

The remark after [1, Prop. 5]: with `Λ_A = I` every constraint is dualized, `Ã = 0` and `b̃ = 0`,
and `Z̃` is the zonotope `{G − Λ_G A, c + Λ_G b}`.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `ΛG` – generator multiplier
* `x` – point

## Hypotheses
* none

## Conclusion
* membership means a unit-box coefficient vector on the dualized generators

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5] at `Λ_A = I`: `Z̃` is the zonotope `{G − Λ_G A, c + Λ_G b}`. -/
theorem ConZonotope.constraintReduce_one_mem_iff {n q h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) (b : Vec ℝ q) (ΛG : Mat ℝ n q)
    (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (ConZonotope.constraintReduce c G A b ΛG 1).construct ↔
      ∃ β : Fin h → ℝ, (∀ j, |β j| ≤ 1) ∧
        x = (c + ΛG *ᵥ b) + ∑ j, β j • (G j - ΛG *ᵥ fun k => A k j) := by -- --- PROOF ---
  unfold ConZonotope.constraintReduce
  rw [ConZonotope.mem_ofMat_iff]
  refine ⟨fun ⟨β, hβ, _, hx⟩ => ⟨β, hβ, hx⟩, fun ⟨β, hβ, hx⟩ => ⟨β, hβ, fun i => ?_, hx⟩⟩
  -- both sides of the constraint vanish: (A − 1·A)β = 0 = b − 1·b
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
