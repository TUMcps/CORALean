module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# One sampled run of an ARX model

`simulate` samples one run rather than enclosing all of them: a point computation, carrying
none of `reach`'s set instances. CORA's `linearARX/simulate` for the normal parametrization
(its `tvp` branch is not modelled): the first `p` outputs are the initial window `y₀`, whose
block `k` holds `y(k)`, and every later one is the recursion
`y(k+1) = B̄₀ u(k+1) + ∑ᵢ Āᵢ y(k+1-i) + B̄ᵢ u(k+1-i)`, which `IsTrajectory.step` states.

## Inputs
* `sys` – ARX system
* `y₀` – initial output window
* `u` – input signal
* `k` – step

## Output
* the output of the run at step `k`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sampled run from the initial window `y₀` under the input signal `u`. -/
def LinearARX.simulate (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy)) (u : ℕ → Vec ℝ du)
    (k : ℕ) : Vec ℝ dy :=
  if hk : k < p then
    -- the first `p` outputs are the initial window's blocks
    fun b => y₀ (finProdFinEquiv (⟨k, hk⟩, b))
  else
    let fromOutputs := ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ sys.simulate y₀ u (k - (i + 1))
    let fromInputs := ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)
    fromOutputs + fromInputs
termination_by k
decreasing_by
  have := i.isLt
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
