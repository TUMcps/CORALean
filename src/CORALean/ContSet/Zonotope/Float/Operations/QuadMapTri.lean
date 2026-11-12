module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.StepOf
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.quadMapTri`, over a floating-point scalar

CORA's `@zonotope/quadMap` (`aux_quadMapSingle`) on the stored floats: with `Z = [c G]` and
`M = Zᵀ Q⁽ⁱ⁾ Z` of every output, the center is `M₀₀ + ½ Σₛ Mₛₛ` and the `N + N(N + 1)/2`
generators are the halved squares `½ Mₛₛ`, then the strict lower triangle of `M + Mᵀ` by columns,
against `Zonotope.quadMap`'s `(N + m + 1)²` through polynomial zonotopes. Center and generators are
rounded down and their gaps are the box, as in `cubMapDep`. An operand whose box is not zero has it
made into generators first. CORA's `nonzeroFilter` and the box for one nonzero output are exact
and left to the caller.

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Output
* zonotope enclosing the quadratic image, with CORA's generators
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The number of off-diagonal generators: column `j` of the strict lower triangle of an `(N + 1) ×
(N + 1)` matrix has `N - j` entries, `N(N + 1)/2` in all. -/
@[step_of Zonotope.quadMapTri]
abbrev Zonotope.step_quadMapTriPairs (N : ℕ) : ℕ := ∑ j : Fin N, (N - j.val)

/-- The column `j` of the `u`-th entry of the strict lower triangle, taken by columns. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriCol (N : ℕ) (u : Fin (Zonotope.step_quadMapTriPairs N)) :
    Fin (N + 1) :=
  ⟨(finSigmaFinEquiv.symm u).1.val, by have := (finSigmaFinEquiv.symm u).1.2; omega⟩

/-- The row `r` of the `u`-th entry of the strict lower triangle, taken by columns. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriRow (N : ℕ) (u : Fin (Zonotope.step_quadMapTriPairs N)) :
    Fin (N + 1) :=
  ⟨(finSigmaFinEquiv.symm u).1.val + 1 + (finSigmaFinEquiv.symm u).2.val, by
    have := (finSigmaFinEquiv.symm u).2.2; have := (finSigmaFinEquiv.symm u).1.2; omega⟩

/-- The entry `(a, b)` of `M = Zᵀ Q Z`, `z_aᵀ Q z_b`, rounded down: the row `Qᵀ z_a` bracketed, then
its dot product with `z_b`. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriEntryDown (Q : Mat 𝕋 n n) {N : ℕ} (Zext : Fin (N + 1) → Vec 𝕋 n)
    (a b : Fin (N + 1)) : 𝕋 :=
  PolyZonotope.quadDown (Zext b) (mulVecDown (fun k j => Q j k) (Zext a))
    (mulVecUp (fun k j => Q j k) (Zext a))

/-- The entry `(a, b)` of `M = Zᵀ Q Z` rounded up. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriEntryUp (Q : Mat 𝕋 n n) {N : ℕ} (Zext : Fin (N + 1) → Vec 𝕋 n)
    (a b : Fin (N + 1)) : 𝕋 :=
  PolyZonotope.quadUp (Zext b) (mulVecDown (fun k j => Q j k) (Zext a))
    (mulVecUp (fun k j => Q j k) (Zext a))

/-- The center `M₀₀ + ½ Σₛ Mₛₛ` of output `i`, rounded down. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriCDown (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 m :=
  fun i =>
    let Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G
    addDown (Zonotope.step_quadMapTriEntryDown (Q i) Zext 0 0)
      (sumDown fun s : Fin Z.h =>
        half (Zonotope.step_quadMapTriEntryDown (Q i) Zext s.succ s.succ))

/-- The center `M₀₀ + ½ Σₛ Mₛₛ` of output `i`, rounded up. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriCUp (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 m :=
  fun i =>
    let Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G
    addUp (Zonotope.step_quadMapTriEntryUp (Q i) Zext 0 0)
      (sumUp fun s : Fin Z.h =>
        half (Zonotope.step_quadMapTriEntryUp (Q i) Zext s.succ s.succ))

/-- The generators of output `i`, rounded down: the halved squares, then `M_rj + M_jr` down the
columns `j` of the strict lower triangle. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriGDown (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) (i : Fin m) :
    Fin (Z.h + Zonotope.step_quadMapTriPairs Z.h) → 𝕋 :=
  let Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G
  Fin.append (fun s : Fin Z.h => half (Zonotope.step_quadMapTriEntryDown (Q i) Zext s.succ s.succ))
    (fun u => addDown
      (Zonotope.step_quadMapTriEntryDown (Q i) Zext (Zonotope.step_quadMapTriRow Z.h u)
        (Zonotope.step_quadMapTriCol Z.h u))
      (Zonotope.step_quadMapTriEntryDown (Q i) Zext (Zonotope.step_quadMapTriCol Z.h u)
        (Zonotope.step_quadMapTriRow Z.h u)))

/-- The generators of output `i`, rounded up. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriGUp (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) (i : Fin m) :
    Fin (Z.h + Zonotope.step_quadMapTriPairs Z.h) → 𝕋 :=
  let Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G
  Fin.append (fun s : Fin Z.h => half (Zonotope.step_quadMapTriEntryUp (Q i) Zext s.succ s.succ))
    (fun u => addUp
      (Zonotope.step_quadMapTriEntryUp (Q i) Zext (Zonotope.step_quadMapTriRow Z.h u)
        (Zonotope.step_quadMapTriCol Z.h u))
      (Zonotope.step_quadMapTriEntryUp (Q i) Zext (Zonotope.step_quadMapTriCol Z.h u)
        (Zonotope.step_quadMapTriRow Z.h u)))

/-- `Z` with its box made into generators, unless the box is already zero (`sup ≤ 0 ≤ inf`). -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriOperand (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  if decide (∀ i, le (Z.I_error.sup i) zero = true ∧ le zero (Z.I_error.inf i) = true) then Z
  else Z.absorbRounding

/-- The enclosure of the quadratic image of an operand whose box is zero: rounded-down center and
generators, and in the box what the rounding left. -/
@[step_of Zonotope.quadMapTri]
def Zonotope.step_quadMapTriCore (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) where
  h := Z.h + Zonotope.step_quadMapTriPairs Z.h
  c := Zonotope.step_quadMapTriCDown Q Z
  G := fun l i => Zonotope.step_quadMapTriGDown Q Z i l
  I_error := (Interval.residual (Zonotope.step_quadMapTriCDown Q Z)
      (Zonotope.step_quadMapTriCUp Q Z) (Zonotope.step_quadMapTriCDown Q Z)).plus
    (Zonotope.generatorError fun i l =>
      subUp (Zonotope.step_quadMapTriGUp Q Z i l) (Zonotope.step_quadMapTriGDown Q Z i l))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `quadMap` of a zonotope: `N + N(N + 1)/2` generators, the squares then the lower
triangle of `M + Mᵀ` by columns. -/
def Zonotope.quadMapTri (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  Zonotope.step_quadMapTriCore Q (Zonotope.step_quadMapTriOperand Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
