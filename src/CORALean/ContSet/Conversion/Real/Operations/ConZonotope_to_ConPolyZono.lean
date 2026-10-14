module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficients of a linear functional on a coordinate space. -/
def ConZonotope.coeffs {h : ℕ} (f : Vec ℝ h →ₗ[ℝ] ℝ) : Vec ℝ h :=
  fun j => f (Pi.single j 1)

/-- The inequality rows, then the equality rows, each read off as coefficients
over the coefficient space. -/
def ConZonotope.conA (cZ : ConZonotope (Vec ℝ n)) : Mat ℝ (cZ.P.m + cZ.P.me) cZ.h :=
  Fin.append (fun i => ConZonotope.coeffs (cZ.P.A i))
    fun i => ConZonotope.coeffs (cZ.P.Ae i)

/-- An inequality gets the free lower bound; an equality is the degenerate
interval. -/
def ConZonotope.conB (cZ : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ (cZ.P.m + cZ.P.me)) :=
  ⟨Fin.append (fun i => -∑ j, |ConZonotope.coeffs (cZ.P.A i) j|) cZ.P.be,
   Fin.append cZ.P.b cZ.P.be⟩

def ConZonotope.conPolyZono (cZ : ConZonotope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) where
  p := cZ.h
  h := cZ.h
  qI := 0
  m := cZ.P.m + cZ.P.me
  q := cZ.h
  c := cZ.c
  G := cZ.G
  E := PolyZonotope.identE cZ.h
  GI := Fin.elim0
  A := ConZonotope.conA cZ
  b := ConZonotope.conB cZ
  R := PolyZonotope.identE cZ.h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
