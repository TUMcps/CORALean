module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.stackRows`

The constraint lists concatenate. Nothing is computed, so nothing rounds: the nominal parts
intersect exactly, as over ℝ. The error boxes are not read: the result carries none, so it
denotes the intersection of the two nominal parts and no more. `HPolytope.intersection` is
this after each box has been folded into its rows.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.stackRows (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := P₁.m + P₂.m
  A := Fin.append P₁.A P₂.A
  b := Fin.append P₁.b P₂.b
  me := P₁.me + P₂.me
  Ae := Fin.append P₁.Ae P₂.Ae
  be := Fin.append P₁.be P₂.be
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
