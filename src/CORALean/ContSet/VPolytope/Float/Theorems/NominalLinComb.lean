import CORALean.ContSet.VPolytope.Float.Operations.LinComb

/-!
# `linComb`'s nominal part is the exact layer's `linComb`

`toReal` and `Fin.append` commute, which is the one fact a concatenated vertex
list needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.nominal_linComb (P₁ P₂ : VPolytope 𝕋 n) :
    nominal (P₁.linComb P₂) = (nominal P₁).linComb (nominal P₂) := by -- --- PROOF ---
  have hV : (fun (l : Fin (P₁.k + P₂.k)) i => toReal ((P₁.linComb P₂).V i l))
      = Fin.append (fun l i => toReal (P₁.V i l)) (fun l i => toReal (P₂.V i l)) := by
    funext l
    refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l <;> funext i <;>
      simp only [VPolytope.linComb, Fin.append_left, Fin.append_right]
  exact congrArg (Real.VPolytope.mk (P₁.k + P₂.k)) hV

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
