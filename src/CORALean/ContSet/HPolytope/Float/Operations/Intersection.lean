module

public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `HPolytope.intersection`

The constraint lists concatenate. When both error boxes are certified to be the origin
(`isErrFree`), that is all: nothing is computed, so nothing rounds, and the intersection is
exact, as over ℝ.

Otherwise a box is not a halfspace, and the intersection of two inflated descriptions has no
nominal-plus-box form: the rows have to carry what the boxes allow. Each inequality is raised by
its own box's support (`bU`). The equalities stay as stored: a point of the intersection reads
within `beRes` of each of them, and `anchorEqs` moves it onto all of them at once, paying the
certified step into the result's error box. Without a certificate for the stacked equalities,
each becomes the two inequalities it stands for, widened by its residual, as `absorbRounding`
writes it. The result is an outer approximation of the intersection of the two sets. `stackRows`
is the concatenation without the folding, exact on the nominal parts.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.intersection (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  if P₁.isErrFree && P₂.isErrFree then P₁.stackRows P₂
  else
    -- the inequalities raised by their boxes, the equalities as stored
    let Q : HPolytope 𝕋 (Vec 𝕋 n) := { P₁.stackRows P₂ with b := Fin.append P₁.bU P₂.bU }
    Q.anchorEqs (Fin.append P₁.beRes P₂.beRes)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
