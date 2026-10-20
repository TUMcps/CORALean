module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter

@[expose] public section

/-!
# `0 ∈ P̂^U(Δt)` when `0 ∈ U₀`

[1, Prop. 11], eq. (20)'s set is a Minkowski sum of linear images of `U₀` and of the interval
product `E(Δt,η)ΔtU₀`. Each holds `0` once `U₀` does, `[1]`'s Alg. 1 taking `U₀ = ⟨0, BG_u⟩`, and so
does the sum, from any lowest order `i₀`.

## Inputs
* `A` – system matrix
* `U0` – input set
* `i0` – start index
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `h0` – origin lies in the input set

## Conclusion
* the origin lies in the particular solution outer approximation

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11], eq. (20): `0 ∈ ⊕_{i₀≤i≤η} ÃᵢU₀ ⊕ E(Δt,η)ΔtU₀` whenever `0 ∈ U₀`. -/
theorem MatExp.zero_mem_particularSolutionOuter (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (h0 : (0 : Vec ℝ n) ∈ U0) (i0 : ℕ) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    (0 : Vec ℝ n) ∈ MatExp.particularSolutionOuter A U0 i0 Δt η := by -- --- PROOF ---
  rw [MatExp.particularSolutionOuter]
  have hsum := Set.finsetSum_mem_finsetSum (Finset.Ico i0 (η + 1))
    (fun i => (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0) (fun _ => 0)
    (fun i _ => ⟨0, h0, by simp⟩)
  simp only [Finset.sum_const_zero] at hsum
  -- the remainder block: the zero matrix at the point `Δt • 0 = 0`
  refine ⟨0, hsum, 0, ⟨0, fun j k => by simp, 0, ?_, by simp⟩, add_zero 0⟩
  simpa using Set.smul_mem_smul_set (a := Δt) h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
