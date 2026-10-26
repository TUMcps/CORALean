module

public import CORALean.NN.Layers.Definitions.TanhRelaxation
public import CORALean.NN.Layers.Theorems.OfAffineConjSound
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.SigmoidRelaxationSound
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

@[expose] public section

/-!
# The tanh relaxation over ℝ is sound

ℝ-only, the relaxation being the exact sigmoid one at the exact doubling: the sigmoid's
soundness transported along the conjugation identity.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the relaxation is sound for tanh
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- ℝ-only, as `ScaleRounding.exact` is: only ℝ stores `r · x` exactly. Both directions are the
product itself. -/
private theorem aux_scaleRounding_exact_sound (r : ℝ) : (ScaleRounding.exact r).IsSound r :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanhRelaxation_sound : tanhRelaxation.IsSound Real.tanh :=
  Relaxation.ofAffineConj_sound sigmoidRelaxation_sound (aux_scaleRounding_exact_sound 2)
    (aux_scaleRounding_exact_sound 2) (by norm_num) (by norm_num)
    (fun t => by
      show Real.tanh t = 2 * sigmoid (2 * t) + -1
      rw [tanh_eq_sigmoid]; ring)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
