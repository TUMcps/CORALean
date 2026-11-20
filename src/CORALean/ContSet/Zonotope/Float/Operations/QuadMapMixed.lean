module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRoundingIfAny
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryDown
public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryUp
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapFilter
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.StepOf
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.quadMapMixed`, over a floating-point scalar

CORA's `@zonotope/quadMap(Z₁, Z₂, Q)` (`aux_quadMapMixed`) on the stored floats: with
`Z₁ = [c₁ G₁]`, `Z₂ = [c₂ G₂]` and `M = Z₁ᵀ Q⁽ⁱ⁾ Z₂` of every output, the entries of `M` in
MATLAB's column-major order are the result, the first one its center and the other
`(N₁ + 1)(N₂ + 1) - 1` its generators. Center and generators are rounded down and their gaps are
the box, as in `quadMapTri`. An operand whose box is not zero has it made into generators first.
Then CORA's `nonzeroFilter`, or the box for one nonzero output (`quadMapFilter`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z₁` – zonotope of the left argument
* `Z₂` – zonotope of the right argument

## Output
* zonotope enclosing `{xᵀ Q⁽ⁱ⁾ y | x ∈ Z₁, y ∈ Z₂}`, with CORA's generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The entry `(a, b)` of `M` at place `t` of the column-major order, `t = a + (N₁ + 1) b`. -/
@[step_of Zonotope.quadMapMixed]
def Zonotope.step_quadMapMixedIdx (N₁ N₂ : ℕ) (t : Fin (N₁ + N₂ * (N₁ + 1) + 1)) :
    Fin (N₂ + 1) × Fin (N₁ + 1) :=
  finProdFinEquiv.symm (Fin.cast (by ring) t)

/-- The entry at place `t` of `M = Z₁ᵀ Q Z₂`, rounded down. -/
@[step_of Zonotope.quadMapMixed]
def Zonotope.step_quadMapMixedEntryDown (Q : Mat 𝕋 n n) (Z₁ Z₂ : Zonotope (Vec 𝕋 n))
    (t : Fin (Z₁.h + Z₂.h * (Z₁.h + 1) + 1)) : 𝕋 :=
  let ba := Zonotope.step_quadMapMixedIdx Z₁.h Z₂.h t
  Zonotope.quadEntryDown Q ((Fin.cons Z₁.c Z₁.G : Fin (Z₁.h + 1) → Vec 𝕋 n) ba.2)
    ((Fin.cons Z₂.c Z₂.G : Fin (Z₂.h + 1) → Vec 𝕋 n) ba.1)

/-- The entry at place `t` of `M = Z₁ᵀ Q Z₂`, rounded up. -/
@[step_of Zonotope.quadMapMixed]
def Zonotope.step_quadMapMixedEntryUp (Q : Mat 𝕋 n n) (Z₁ Z₂ : Zonotope (Vec 𝕋 n))
    (t : Fin (Z₁.h + Z₂.h * (Z₁.h + 1) + 1)) : 𝕋 :=
  let ba := Zonotope.step_quadMapMixedIdx Z₁.h Z₂.h t
  Zonotope.quadEntryUp Q ((Fin.cons Z₁.c Z₁.G : Fin (Z₁.h + 1) → Vec 𝕋 n) ba.2)
    ((Fin.cons Z₂.c Z₂.G : Fin (Z₂.h + 1) → Vec 𝕋 n) ba.1)

/-- The entries of `M` of operands whose boxes are zero: the first the center, the others the
generators, all rounded down, and in the box what the rounding left. -/
@[step_of Zonotope.quadMapMixed]
def Zonotope.step_quadMapMixedCore (Q : Fin m → Mat 𝕋 n n) (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) where
  h := Z₁.h + Z₂.h * (Z₁.h + 1)
  c := fun i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ 0
  G := fun l i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ l.succ
  I_error := (Interval.residual (fun i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ 0)
      (fun i => Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ 0)
      (fun i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ 0)).plus
    (Zonotope.generatorError fun i l =>
      subUp (Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ l.succ)
        (Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ l.succ))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `quadMap(Z₁, Z₂, Q)`: the entries of `Z₁ᵀ Q⁽ⁱ⁾ Z₂`, then its `nonzeroFilter`. -/
def Zonotope.quadMapMixed (Q : Fin m → Mat 𝕋 n n) (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  let Zq := (Zonotope.step_quadMapMixedCore Q Z₁.absorbRoundingIfAny
    Z₂.absorbRoundingIfAny).materialise                           -- the entries computed once
  Zq.quadMapFilter Q                            -- nonzeroFilter(Gquad) or sum(abs(Gquad),2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
