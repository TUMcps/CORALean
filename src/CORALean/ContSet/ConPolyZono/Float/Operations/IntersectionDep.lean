module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeCons
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.And
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.intersectionDep`

Sound where both independent blocks are empty; `intersection` arranges that. Its constraint is
the two sets' side by side (`PolyLevelSet.cartProd`) stacked on the agreement rows `agreeCons`
(`PolyLevelSet.andRows`), each held to its interval. Keeps
`cPZ₁`'s error box and only `cPZ₁`'s generator block: the point it denotes is
`y₁ + e₁`, and `cPZ₂` enters through the constraint system alone, its generator
columns kept at `zero` so the agreement rows can read the second point.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Sound where both independent blocks are empty; `intersection` arranges that. -/
def ConPolyZono.intersectionDep (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := 0
  c := cPZ₁.c
  G := Fin.append cPZ₁.G fun _ _ => zero
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  -- each set's rows on its own factors, then the agreement rows, each held to its interval
  cons := (cPZ₁.cons.cartProd cPZ₂.cons).andRows (ConPolyZono.agreeCons cPZ₁ cPZ₂)
  cons_eq := Real.LevelSet.append_op_eq (Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq)
    fun _ => rfl
  cons_dom := Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom
  I_error := cPZ₁.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
