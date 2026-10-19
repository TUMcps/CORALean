module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.StarSet.Real.StarSet
public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars

@[expose] public section

/-!
# A constrained polynomial zonotope as a star set with a polynomial predicate

A star set is linear in its coefficients, so the coefficients are the factors `α`, the independent
coefficients `β` and one more per dependent generator, `z`, standing for its monomial: the point
is `c + Σ GIⱼ βⱼ + Σ Gₗ zₗ`, and the predicate, a `PolyLevelSet` on `(α, β, z)` over the unit box,
is two systems stacked by `PolyLevelSet.and_`: the constraint `A μ_R(α) = b`, `cons` padded with
`β` and `z` (`starConsRows`), and `zₗ = μ_{E}(α)ₗ` (`starGenRows`). The cube `|α|, |β| ≤ 1` is the
predicate's domain box, and `z` lies in it too, a monomial of the cube being in `[-1, 1]`. The
star set's own box is the same unit box: redundant here, it is what every star set carries, and the
predicate's is what every polynomial level set carries.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint on the factors, blind to `β` and `z`: `cons` padded with both, each in the unit
box. -/
def ConPolyZono.starConsRows (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyLevelSet (cPZ.p + cPZ.qI + cPZ.h) :=
  (cPZ.cons.padVars (Interval.unit cPZ.qI)).padVars (Interval.unit cPZ.h)

/-- `zₗ - μ_{E}(α)ₗ = 0` on the unit box: each `z` is its generator's monomial. -/
def ConPolyZono.starGenRows (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyLevelSet (cPZ.p + cPZ.qI + cPZ.h) where
  m := cPZ.h
  q := cPZ.h + cPZ.h
  A := fun l => Fin.append (fun l' => if l' = l then -1 else 0) (fun l' => if l' = l then 1 else 0)
  R := PolyZonotope.plusE (ConPolyZono.padE cPZ.E cPZ.qI) (PolyZonotope.identE cPZ.h)
  b := fun _ => 0
  op := fun _ => .eq
  dom := Interval.unit _

/-- The coefficients `(α, β, z)`, the basis `0` on `α`, `GI` on `β`, `G` on `z`, and the two
systems as the predicate. -/
def ConPolyZono.starSet (cPZ : ConPolyZono (Vec ℝ n)) : StarSet PolyLevelSet n where
  m := cPZ.p + cPZ.qI + cPZ.h
  c := cPZ.c
  G := fun i => Fin.append (Fin.append (fun _ => 0) fun j => cPZ.GI j i) fun l => cPZ.G l i
  dom := Interval.unit _
  pred := cPZ.starConsRows.and_ cPZ.starGenRows

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
