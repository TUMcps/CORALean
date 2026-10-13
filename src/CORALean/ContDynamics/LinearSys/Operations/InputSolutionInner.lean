module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

@[expose] public section

/-!
# The inner approximation of the particular solution over one step

[1, Prop. 1] writes this `A⁻¹(e^{AΔt} - I_n)S`, and says in the same breath that
where `A` is singular the inverse is to be integrated into the power series
instead. `expIntegral` is that series, `∑ᵢ Aⁱ Δt^{i+1}/(i+1)!`, so no
invertibility hypothesis is needed here and none is carried downstream.

It is an inner approximation because it is exactly what the *constant* inputs of
`S` contribute: `expIntegral A Δt *ᵥ s = ∫₀^{Δt} e^{A(Δt-σ)}s dσ`. A plain image
and not a `Mtimes`, since `Mtimes` only ever over-approximates.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Everything a constant input of `U` contributes over `[0, Δt]`. -/
noncomputable def LinearSys.inputSolutionInner (sys : LinearSys 𝕋 n) (U : S n) (Δt : ℝ) :
    Set (Vec ℝ n) :=
  (fun s => MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ s) '' construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
