module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope, over a
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows, then the equality rows; entries copied. -/
def ConZonotope.conA (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Mat 𝕋 (cZ.P.m + cZ.P.me) cZ.h :=
  Fin.append cZ.P.A cZ.P.Ae

/-- The upper bounds are `P`'s own. An inequality has no lower bound, and gets
the free one: no factor leaves `[-1,1]`, so no row falls below minus its row sum
of absolute values, which `radius` computes upward. -/
def ConZonotope.conB (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 (cZ.P.m + cZ.P.me)) :=
  ⟨Fin.append (fun i => neg (radius cZ.P.A i)) cZ.P.be.inf,
   Fin.append cZ.P.b cZ.P.be.sup⟩

def ConZonotope.conPolyZono (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cZ.h
  h := cZ.h
  qI := 0
  m := cZ.P.m + cZ.P.me
  q := cZ.h
  c := cZ.c
  G := cZ.G
  E := Real.PolyZonotope.identE cZ.h
  GI := Fin.elim0
  A := ConZonotope.conA cZ
  b := ConZonotope.conB cZ
  R := Real.PolyZonotope.identE cZ.h
  I_error := cZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
