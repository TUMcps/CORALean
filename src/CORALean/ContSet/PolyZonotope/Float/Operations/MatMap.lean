module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinE
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.MatGeneratorError
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `PolyZonotope.matMap`, over a floating-point scalar

CORA's `matMap(pZ1, pZ2, n, k, m)` as `Real.PolyZonotope.matMap` has it — `bilin` at matrix
multiplication over shared factors, plus the independent cross terms — with every product of two
generators stored rounded down (`matMulDown`) and the gap to the upper rounding charged to the
error box. The operands' own error boxes enter by interval-matrix products against hulls of the
operands: `(N₁ + e₁)(N₂ + e₂) = N₁N₂ + N₁e₂ + e₁(N₂ + e₂)`, `N` bounded entrywise by the sum
of its generators' absolute values.

## Inputs
* `pZ₁` – first matrix polynomial zonotope
* `pZ₂` – second matrix polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* matrix polynomial zonotope of their product
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k m : ℕ}
variable {α β γ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type}

/-- The center, then the dependent generators. -/
def PolyZonotope.aux_extGens (pZ : PolyZonotope α) : Fin (pZ.h + 1) → α := Fin.cons pZ.c pZ.G

end


/-- `f` at each pair of extended generators, the pairs indexed by `finProdFinEquiv`. -/
def PolyZonotope.aux_pairG (f : α → β → γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → γ :=
  fun l => f (PolyZonotope.aux_extGens pZ₁ (finProdFinEquiv.symm l).1)
    (PolyZonotope.aux_extGens pZ₂ (finProdFinEquiv.symm l).2)

/-- The pairs `f (GI₁ j) (ext₂ l)`, `f (GI₁ j) (GI₂ l)`, `f (ext₁ l) (GI₂ j)` as one list. -/
def PolyZonotope.aux_pairGI (f : α → β → γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q) → γ :=
  Fin.append
    (Fin.append
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1)
        (PolyZonotope.aux_extGens pZ₂ (finProdFinEquiv.symm l).2))
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1) (pZ₂.GI (finProdFinEquiv.symm l).2)))
    (fun l => f (PolyZonotope.aux_extGens pZ₁ (finProdFinEquiv.symm l).1)
      (pZ₂.GI (finProdFinEquiv.symm l).2))


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.matMap (pZ₁ : PolyZonotope (Mat 𝕋 n k)) (pZ₂ : PolyZonotope (Mat 𝕋 k m))
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (Mat 𝕋 n m) :=
  -- the rounding of every stored product, dependent then independent
  let gap := PolyZonotope.matGeneratorError
    (Fin.append (PolyZonotope.aux_pairG matMulDiff pZ₁ pZ₂)
      (PolyZonotope.aux_pairGI matMulDiff pZ₁ pZ₂))
  -- the operands' hulls: every generator, center included, at a coefficient in `[-1, 1]`
  let H₁ := PolyZonotope.matGeneratorError (Fin.append (PolyZonotope.aux_extGens pZ₁) pZ₁.GI)
  let H₂ := PolyZonotope.matGeneratorError (Fin.append (PolyZonotope.aux_extGens pZ₂) pZ₂.GI)
  -- the operands' error boxes: `N₁ e₂ + e₁ (N₂ + e₂)`
  let errs := Interval.matPlus (Interval.matMul H₁ pZ₂.I_error)
    (Interval.matMul pZ₁.I_error (Interval.matPlus H₂ pZ₂.I_error))
  { p := pZ₁.p
    h := (pZ₁.h + 1) * (pZ₂.h + 1)
    q := pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q
    c := fun _ _ => zero
    G := PolyZonotope.aux_pairG matMulDown pZ₁ pZ₂
    E := PolyZonotope.bilinE pZ₁ pZ₂ hp
    GI := PolyZonotope.aux_pairGI matMulDown pZ₁ pZ₂
    I_error := Interval.matPlus gap errs }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
