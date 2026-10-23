module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstraintReduceSumSmulMulVec
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff

@[expose] public section

/-!
# `ConZonotope.constraintReduce` encloses

[1, Prop. 5]: `Z ⊂ Z̃` for every `Λ_G` and `Λ_A`. The paper's `Z = {G, c, A, b}` is `ofMat c G A b`,
whose constraint is the polytope `Aξ = b` on the coefficients; the proof is the paper's, with
`z = Gξ + c` and `0 = b − Aξ` added back through `Λ_G` and `Λ_A`. The remark that `Λ_A = I`
leaves a zonotope is `constraintReduce_one_mem_iff`.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `ΛG` – generator multiplier
* `ΛA` – constraint multiplier

## Hypotheses
* none

## Conclusion
* the original set is contained in the reduced set

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

/-- [1, Prop. 5]: `Z ⊂ Z̃` for every `Λ_G ∈ ℝ^{n×nc}` and `Λ_A ∈ ℝ^{nc×nc}`. -/
theorem ConZonotope.constraintReduce_outer {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (ΛG : Mat ℝ n q) (ΛA : Mat ℝ q q) : -- --- CONCL ---
    (ConZonotope.ofMat c G A b).construct
      ⊆ (ConZonotope.constraintReduce c G A b ΛG ΛA).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hAβ, rfl⟩ := ConZonotope.mem_ofMat_iff.mp hx
  have hAβ' : A *ᵥ β = b := funext hAβ
  refine ConZonotope.mem_ofMat_iff.mpr ⟨β, hβ, fun i => ?_, ?_⟩
  · -- (A − Λ_A A)β = Aβ − Λ_A (Aβ) = b − Λ_A b
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hAβ']
  · -- the value, with `Λ_G (b − Aβ) = 0` added
    funext i
    have hs := ConZonotope.sum_smul_mulVec_columns ΛG A β i
    rw [hAβ'] at hs
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      mul_sub, Finset.sum_sub_distrib] at hs ⊢
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
