module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope, over a floating-point scalar

The coefficients become the factors, one each and to the first power, and every row of the
coefficient polytope one constraint row, held to its enclosure over the unit cube (`conB`) as a
right-hand side, the lower end, and a slack, the width above it rounded up. The slack reads the
enclosure wider still, which an outer conversion may; the exact layer instead adds a slack factor
per row (`Real.ConZonotope.conPolyZono`).
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows, then the equality rows; entries copied. -/
def ConZonotope.conA (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Mat 𝕋 (cZ.P.m + cZ.P.me) cZ.h :=
  Fin.append cZ.P.A cZ.P.Ae

/-- Each row's enclosure over the unit cube: the upper bounds are `P`'s own, widened by their
slack. An inequality has no lower bound, and gets the free one: no factor leaves `[-1,1]`, so no
row falls below minus its row sum of absolute values, which `radius` computes upward. -/
def ConZonotope.conB (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 (cZ.P.m + cZ.P.me)) :=
  ⟨Fin.append (-(radius cZ.P.A)) fun k => subDown (cZ.P.be k) (absolute (cZ.P.be_error k)),
   Fin.append (fun k => addUp (cZ.P.b k) (absolute (cZ.P.b_error k)))
     fun k => addUp (cZ.P.be k) (absolute (cZ.P.be_error k))⟩

def ConZonotope.conPolyZono (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cZ.h
  h := cZ.h
  qI := 0
  c := cZ.c
  G := cZ.G
  E := Real.PolyZonotope.identE cZ.h
  GI := Fin.elim0
  -- each row held to its enclosure: its lower end, and the width above it
  cons := ⟨cZ.P.m + cZ.P.me, cZ.h, ConZonotope.conA cZ, Real.PolyZonotope.identE cZ.h,
    (ConZonotope.conB cZ).inf,
    fun k => subUp ((ConZonotope.conB cZ).sup k) ((ConZonotope.conB cZ).inf k), fun _ => .eq,
    Interval.unit cZ.h⟩
  cons_eq _ := rfl
  cons_dom := rfl
  I_error := cZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
