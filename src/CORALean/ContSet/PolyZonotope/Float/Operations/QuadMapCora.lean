module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
public import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
public import CORALean.ContSet.PolyZonotope.Float.Operations.FoldConstants
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryDown
public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryUp
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapMixed
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTriFiltered
public import CORALean.Global.StepOf
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `PolyZonotope.quadMapCora`, over a floating-point scalar

CORA's `@polyZonotope/quadMap` as CORA.cpp computes it. With `[c G]` and the exponents `[0 E]`,
the products of every two columns `j ≤ k` (`j` outer) are the dependent generators, `Mⱼⱼ` and
`Mⱼₖ + Mₖⱼ` for `M = [c G]ᵀ Q⁽ⁱ⁾ [c G]`, with the exponents `Eⱼ + Eₖ`; they are rounded down and
their gaps are the box. The independent part `R = (0, GI)` (the box with it) is enclosed by the
zonotope quadratic maps of `R`, of the dependent part `D` (as a zonotope) against `R`, and of `R`
against `D`, added up (`Zonotope.plus`). Then CORA's constructor merges equal exponents
(`construct`) and the constant column goes into the center (`foldConstants`). Without dependent
generators it is the map of the zonotope `(c, GI)`. The pieces are materialised (computed once).

## Inputs
* `Q` – quadratic form per output coordinate
* `order` – column order of CORA's constructor
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope enclosing the quadratic image, with CORA's generators
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

/-- The number of products `j ≤ k` of `N + 1` columns: `N + 1 - j` for each `j`. -/
@[step_of PolyZonotope.quadMapCora]
abbrev PolyZonotope.step_quadMapCoraPairs (N : ℕ) : ℕ := ∑ j : Fin (N + 1), (N + 1 - j.val)

/-- The product `u` as the columns `(j, j + r)`, `j` outer. -/
@[step_of PolyZonotope.quadMapCora]
def PolyZonotope.step_quadMapCoraPair (N : ℕ) (u : Fin (PolyZonotope.step_quadMapCoraPairs N)) :
    Fin (N + 1) × Fin (N + 1) :=
  let σ := finSigmaFinEquiv.symm u
  (σ.1, ⟨σ.1.val + σ.2.val, by have := σ.2.2; omega⟩)

/-- The generator of product `u` in output `i`, rounded down: `Mⱼⱼ` or `Mⱼₖ + Mₖⱼ`. -/
@[step_of PolyZonotope.quadMapCora]
def PolyZonotope.step_quadMapCoraGDown (Q : Mat 𝕋 n n) {N : ℕ} (Zext : Fin (N + 1) → Vec 𝕋 n)
    (u : Fin (PolyZonotope.step_quadMapCoraPairs N)) : 𝕋 :=
  let jk := PolyZonotope.step_quadMapCoraPair N u
  if jk.1 = jk.2 then Zonotope.quadEntryDown Q (Zext jk.1) (Zext jk.1)
  else addDown (Zonotope.quadEntryDown Q (Zext jk.1) (Zext jk.2))
    (Zonotope.quadEntryDown Q (Zext jk.2) (Zext jk.1))

/-- The generator of product `u` in output `i`, rounded up. -/
@[step_of PolyZonotope.quadMapCora]
def PolyZonotope.step_quadMapCoraGUp (Q : Mat 𝕋 n n) {N : ℕ} (Zext : Fin (N + 1) → Vec 𝕋 n)
    (u : Fin (PolyZonotope.step_quadMapCoraPairs N)) : 𝕋 :=
  let jk := PolyZonotope.step_quadMapCoraPair N u
  if jk.1 = jk.2 then Zonotope.quadEntryUp Q (Zext jk.1) (Zext jk.1)
  else addUp (Zonotope.quadEntryUp Q (Zext jk.1) (Zext jk.2))
    (Zonotope.quadEntryUp Q (Zext jk.2) (Zext jk.1))

/-- The quadratic map of the independent part: the maps of `R = (0, GI)` and of `D` against `R`
and `R` against `D`, added up; nothing where `GI` is empty and the box zero. -/
@[step_of PolyZonotope.quadMapCora]
def PolyZonotope.step_quadMapCoraIndep (Q : Fin m → Mat 𝕋 n n) (R D : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  if R.h = 0 ∧ ∀ i, le (R.I_error.sup i) zero = true ∧ le zero (R.I_error.inf i) = true then
    ⟨0, fun _ => zero, Fin.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
  else ((R.quadMapTriFiltered Q).plus (D.quadMapMixed Q R)).plus (R.quadMapMixed Q D)

/-- The products of the columns of `[c G]` with the exponents `[0 E]`, and the independent part
`IR` as the independent generators. -/
@[step_of PolyZonotope.quadMapCora]
def PolyZonotope.step_quadMapCoraProducts (Q : Fin m → Mat 𝕋 n n) {p N : ℕ}
    (Zext : Fin (N + 1) → Vec 𝕋 n) (Eext : Fin p → Fin (N + 1) → ℕ) (IR : Zonotope (Vec 𝕋 m)) :
    PolyZonotope (Vec 𝕋 m) where
  p := p
  h := PolyZonotope.step_quadMapCoraPairs N
  q := IR.h
  c := IR.c
  G := fun u i => PolyZonotope.step_quadMapCoraGDown (Q i) Zext u
  E := fun k u => Eext k (PolyZonotope.step_quadMapCoraPair N u).1
    + Eext k (PolyZonotope.step_quadMapCoraPair N u).2
  GI := IR.G
  I_error := IR.I_error.plus (Zonotope.generatorError fun i u =>
    subUp (PolyZonotope.step_quadMapCoraGUp (Q i) Zext u)
      (PolyZonotope.step_quadMapCoraGDown (Q i) Zext u))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `quadMap` of a polynomial zonotope: the products of the dependent part, the zonotope
maps of the independent part, CORA's constructor and the constant into the center. -/
def PolyZonotope.quadMapCora (Q : Fin m → Mat 𝕋 n n) (order : ℕ → Array (Array ℕ) → Array ℕ)
    (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 m) :=
  if pZ.h = 0 then
    -- no dependent part: the quadratic map of the zonotope (c, GI)
    let Zr := Zonotope.quadMapTriFiltered Q ⟨pZ.q, pZ.c, pZ.GI, pZ.I_error⟩
    ⟨pZ.p, 0, Zr.h, Zr.c, Fin.elim0, fun _ => Fin.elim0, Zr.G, Zr.I_error⟩
  else
    let Zext : Fin (pZ.h + 1) → Vec 𝕋 n := Fin.cons pZ.c pZ.G                -- [c, G]
    let Eext : Fin pZ.p → Fin (pZ.h + 1) → ℕ := fun k => Fin.cons 0 (pZ.E k)   -- [0, E]
    let R : Zonotope (Vec 𝕋 n) := ⟨pZ.q, fun _ => zero, pZ.GI, pZ.I_error⟩   -- zonotope(0, GI)
    let D := ({ pZ with q := 0, GI := Fin.elim0, I_error := ⟨fun _ => zero, fun _ => zero⟩ :
      PolyZonotope (Vec 𝕋 n)}.construct order).zonotopeFold.materialise    -- Dnoc
    let IR := (PolyZonotope.step_quadMapCoraIndep Q R D).materialise      -- A + B + C
    let S := (PolyZonotope.step_quadMapCoraProducts Q Zext Eext IR).materialise  -- Gquad
    (S.construct order).materialise.foldConstants

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
