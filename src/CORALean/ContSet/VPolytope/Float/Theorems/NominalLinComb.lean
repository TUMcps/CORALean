module

public import CORALean.ContSet.VPolytope.Float.Operations.LinComb

@[expose] public section

/-!
# `linComb`'s nominal part is the exact layer's `linComb`

`toReal` and `Fin.append` commute, which is the one fact a concatenated vertex
list needs.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* the nominal part of `linComb` is the real `linComb` of the nominal parts
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.nominal_linComb (P₁ P₂ : VPolytope (Vec 𝕋 n)) : -- --- CONCL ---
    nominal (P₁.linComb P₂) = (nominal P₁).linComb (nominal P₂) := by -- --- PROOF ---
  have hV : (fun (l : Fin (P₁.k + P₂.k)) i => toReal ((P₁.linComb P₂).V l i))
      = Fin.append (fun l i => toReal (P₁.V l i)) (fun l i => toReal (P₂.V l i)) := by
    funext l
    refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l <;> funext i <;>
      simp only [VPolytope.linComb, Fin.append_left, Fin.append_right]
  exact congrArg (Real.VPolytope.mk (P₁.k + P₂.k)) hV

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
