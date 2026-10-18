module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A constrained polynomial zonotope as a star set with a polynomial predicate

A star set is linear in its coefficients, so the coefficients are the factors `α`, the independent
coefficients `β` and one more per dependent generator, `z`, standing for its monomial: the point
is `c + Σ GIⱼ βⱼ + Σ Gₗ zₗ`, and the predicate, a `PolyLevelSet` on `(α, β, z)`, is three systems
stacked by `PolyLevelSet.and_`: the cube, `αₖ² ≤ 1` and `βⱼ² ≤ 1` (`starBoxRows`); the
constraint `A μ_R(α) = b` (`starConsRows`); and `zₗ = μ_{E}(α)ₗ` (`starGenRows`). The rows `≤`
and `=` are both needed, which is what the predicate's operators are for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cube on the factors and the independent coefficients: `xₖ² - 1 ≤ 0`, `z` unconstrained. -/
def ConPolyZono.starBoxRows (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyLevelSet (cPZ.p + cPZ.qI + cPZ.h) where
  m := cPZ.p + cPZ.qI
  q := cPZ.p + cPZ.qI
  A := fun i j => if i = j then 1 else 0
  R := ConPolyZono.padE (fun k j => if k = j then 2 else 0) cPZ.h
  b := fun _ => 1
  op := fun _ => .le

/-- The constraint system on the factors, blind to `β` and `z`. -/
def ConPolyZono.starConsRows (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyLevelSet (cPZ.p + cPZ.qI + cPZ.h) where
  m := cPZ.m
  q := cPZ.q
  A := cPZ.A
  R := ConPolyZono.padE (ConPolyZono.padE cPZ.R cPZ.qI) cPZ.h
  b := cPZ.b
  op := fun _ => .eq

/-- `zₗ - μ_{E}(α)ₗ = 0`: each `z` is its generator's monomial. -/
def ConPolyZono.starGenRows (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyLevelSet (cPZ.p + cPZ.qI + cPZ.h) where
  m := cPZ.h
  q := cPZ.h + cPZ.h
  A := fun l => Fin.append (fun l' => if l' = l then -1 else 0) (fun l' => if l' = l then 1 else 0)
  R := PolyZonotope.plusE (ConPolyZono.padE cPZ.E cPZ.qI) (PolyZonotope.identE cPZ.h)
  b := fun _ => 0
  op := fun _ => .eq

/-- The coefficients `(α, β, z)`, the basis `0` on `α`, `GI` on `β`, `G` on `z`, and the three
systems as the predicate. -/
def ConPolyZono.starSet (cPZ : ConPolyZono (Vec ℝ n)) : StarSet PolyLevelSet n where
  m := cPZ.p + cPZ.qI + cPZ.h
  c := cPZ.c
  G := fun i => Fin.append (Fin.append (fun _ => 0) fun j => cPZ.GI j i) fun l => cPZ.G l i
  pred := cPZ.starBoxRows.and_ (cPZ.starConsRows.and_ cPZ.starGenRows)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
