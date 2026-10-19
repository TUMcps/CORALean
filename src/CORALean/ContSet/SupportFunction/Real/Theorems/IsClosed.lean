module

public import CORALean.Global.Tensor
public import CORALean.ContSet.SupportFunction.Real.SupportFunction
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# A support function denotes a closed set

The set is an intersection of the closed halfspaces `{x | ℓ x ≤ h ℓ}`: a linear functional on `Vec ℝ
n` is continuous, and `{t | t ≤ b}` is closed in the extended reals. So a convex set that is not
closed, such as an open box, is the set of no support function: it shares its support function with
its closure.

## Inputs
* `S` – support function

## Hypotheses
* none

## Conclusion
* a support function denotes a closed set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SupportFunction.isClosed_construct (S : SupportFunction (Vec ℝ n)) :
    IsClosed S.construct := by -- --- PROOF ---
  -- the set is the intersection over the functionals of the preimage of `(-∞, h ℓ]`
  have : S.construct = ⋂ ℓ : Vec ℝ n →ₗ[ℝ] ℝ, (fun x => (ℓ x : EReal)) ⁻¹' Set.Iic (S.h ℓ) := by
    ext x
    simp [SupportFunction.construct]
  rw [this]
  refine isClosed_iInter fun ℓ => isClosed_Iic.preimage ?_
  exact continuous_coe_real_ereal.comp (LinearMap.continuous_of_finiteDimensional ℓ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
