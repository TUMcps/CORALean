module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope

The coefficients become the factors, one each and to the first power, and every row of the
coefficient polytope one constraint row, held to the interval `[lo, hi]` it may take over the unit
cube: an equality to its point `be`, an inequality `a β ≤ b` to `[min(-Σ|aⱼ|, b), b]`, the least
it reaches capped by `b` so that a row no point meets stays empty. A row of a constrained
polynomial zonotope is an equation, so each interval is `ConPolyZono.relax` at its midpoint and
radius: a slack factor per row. Held to these intervals the rows say of the coefficients what the
polytope says (`ConZonotope.conRows_iff`).

## Inputs
* `h` – coordinate dimension
* `f` – linear functional

## Output
* coefficient vector of the functional
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   19-October-2026
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

/-- The least each row can be given over the unit cube: an inequality's `-Σ|aⱼ|` capped by its
`b`, an equality's `be`. -/
noncomputable def ConZonotope.conLo (cZ : ConZonotope (Vec ℝ n)) : Vec ℝ (cZ.P.m + cZ.P.me) :=
  Fin.append (fun i => min (-∑ j, |ConZonotope.coeffs (cZ.P.A i) j|) (cZ.P.b i)) cZ.P.be

/-- The most each row is allowed: `b` for an inequality, `be` for an equality. -/
def ConZonotope.conHi (cZ : ConZonotope (Vec ℝ n)) : Vec ℝ (cZ.P.m + cZ.P.me) :=
  Fin.append cZ.P.b cZ.P.be

/-- Each row held to `[conLo, conHi]`, as its midpoint relaxed by its radius. -/
noncomputable def ConZonotope.conPolyZono (cZ : ConZonotope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  ConPolyZono.relax
    { p := cZ.h
      h := cZ.h
      qI := 0
      c := cZ.c
      G := cZ.G
      E := PolyZonotope.identE cZ.h
      GI := Fin.elim0
      cons := ⟨cZ.P.m + cZ.P.me, cZ.h, ConZonotope.conA cZ, PolyZonotope.identE cZ.h,
        fun i => (ConZonotope.conLo cZ i + ConZonotope.conHi cZ i) / 2, fun _ => .eq,
        Interval.unit cZ.h⟩
      cons_eq := fun _ => rfl
      cons_dom := rfl }
    (fun i => (ConZonotope.conHi cZ i - ConZonotope.conLo cZ i) / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
