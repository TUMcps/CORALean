module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.Midpoint
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.Pick

@[expose] public section

/-!
# `PolyZonotope.encloseShared`

CORA's `enclose(pZ, pZ2)` of two sets with the same identifiers and exponents, which is the
segment between the two sets at each value of the factors: `G = [0.5*G1 + 0.5*G2, 0.5*G1 -
0.5*G2, 0.5*c1 - 0.5*c2]` over the exponents of the first set, the second set's generators taken
over the same columns, one new factor for the position on the segment, and the independent
generators those of the enclosure of the two zonotopes about the origin. The second set enters
by its generators at the first set's columns, which is the second set when its exponent matrix is
the first one's; the theorem says so.

## Inputs
* `A` – first polynomial zonotope
* `B` – second polynomial zonotope

## Hypotheses
* `hh` – both have the same number of dependent generators

## Output
* polynomial zonotope enclosing the segments between the points of both
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p h : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

-- file-local: only `encloseShared` below needs these
/-- The new factor is the last row. -/
@[step_of PolyZonotope.encloseShared]
def PolyZonotope.step_encloseE (E : Fin p → Fin h → ℕ) : Fin (p + 1) → Fin (h + h + 1) → ℕ :=
  fun k => Fin.lastCases (motive := fun _ => Fin (h + h + 1) → ℕ)
    (Fin.append (Fin.append (fun _ => 0) (fun _ => 1)) (fun _ : Fin 1 => 1))
    (fun k' => Fin.append (Fin.append (E k') (E k')) (fun _ : Fin 1 => 0)) k

/-- The sums, the differences, and the difference of the centers. -/
@[step_of PolyZonotope.encloseShared]
def PolyZonotope.step_encloseGen (c₁ c₂ : Vec 𝕋 n) (g₁ g₂ : Fin h → Vec 𝕋 n) :
    Fin (h + h + 1) → Vec 𝕋 n :=
  Fin.append (Fin.append (fun l => PolyZonotope.midpoint (g₁ l) (g₂ l))
    (fun l => PolyZonotope.halfDiff (g₁ l) (g₂ l))) (fun _ => PolyZonotope.halfDiff c₁ c₂)

/-- The gaps of the sums, of the differences, and of the difference of the centers. -/
@[step_of PolyZonotope.encloseShared]
def PolyZonotope.step_encloseGap (c₁ c₂ : Vec 𝕋 n) (g₁ g₂ : Fin h → Vec 𝕋 n) :
    Fin (h + h + 1) → Vec 𝕋 n :=
  Fin.append (Fin.append
    (fun l i => subUp (half (addUp (g₁ l i) (g₂ l i))) (half (addDown (g₁ l i) (g₂ l i))))
    (fun l i => subUp (half (subUp (g₁ l i) (g₂ l i))) (half (subDown (g₁ l i) (g₂ l i)))))
    (fun _ i => subUp (half (subUp (c₁ i) (c₂ i))) (half (subDown (c₁ i) (c₂ i))))

/-- The enclosure of the independent parts, CORA's `[(Gcut+Gequal)/2, cG, (Gcut-Gequal)/2]` (the
center column in the middle) when both have as many generators, `Zonotope.linComb`'s otherwise. -/
@[step_of PolyZonotope.encloseShared]
def PolyZonotope.step_encloseIndep (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let Z := Zonotope.linComb Z₁ Z₂
  if Z₁.h = Z₂.h then
    Z.pick Z.h fun t =>
      if t.val < Z₁.h then t.val else if t.val = Z₁.h then Z₁.h + Z₂.h else t.val - 1
  else Z


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.encloseShared (A B : PolyZonotope (Vec 𝕋 n)) (hh : B.h = A.h) :
    PolyZonotope (Vec 𝕋 n) :=
  -- the second set's generators over the first set's columns
  let g₂ : Fin A.h → Vec 𝕋 n := fun l => B.G (Fin.cast hh.symm l)
  -- `Z = enclose(zonotope([0, GI1]), zonotope([0, GI2]))`
  let Z : Zonotope (Vec 𝕋 n) :=
    PolyZonotope.step_encloseIndep ⟨A.q, fun _ => zero, A.GI, Interval.origin n⟩
      ⟨B.q, fun _ => zero, B.GI, Interval.origin n⟩
  { p := A.p + 1
    h := A.h + A.h + 1
    q := Z.h
    c := PolyZonotope.midpoint A.c B.c
    G := PolyZonotope.step_encloseGen A.c B.c A.G g₂
    E := PolyZonotope.step_encloseE A.E
    GI := Z.G
    I_error := ((A.I_error.linComb B.I_error).plus (PolyZonotope.midpointResidual A.c B.c)).plus
      ((PolyZonotope.generatorError fun i l => PolyZonotope.step_encloseGap A.c B.c A.G g₂ l i).plus
        (Z.I_error.plus (Interval.point Z.c))) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
