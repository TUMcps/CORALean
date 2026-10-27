module

public import CORALean.ContSet.SpectraShadow.Float.Operations.AbsorbRounding
public import CORALean.Global.BlockDiag
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `SpectraShadow.inter`

CORA's `@spectraShadow/and_`, `'exact'` branch, over a floating-point scalar: each shadow's
error box absorbed into its inequality (`absorbRounding`), then the two tied to one point
(`step_tieInter`). Nothing is computed: every stored entry is a stored float, its exact negation,
`zero` or `one`. Stated as an enclosure only; the error box of the result is the origin.

## Inputs
* `S₁` – spectrahedral shadow
* `S₂` – spectrahedral shadow

## Output
* the intersection of both shadows with absorbed error boxes, tied to one point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
open FloatOps

@[step_of SpectraShadow.inter]
def SpectraShadow.step_tieInter (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let unit : Fin n → Vec 𝕋 n := fun i r => if r = i then one else zero
  let zeroV : Vec 𝕋 (n + n) := fun _ => zero
  -- `z - c - Gβ = 0` as that expression and its negation: constants, `β` and `z` coefficients
  let tie₁Const : Vec 𝕋 (n + n) := Fin.append (-S₁.c) S₁.c
  let tie₂Const : Vec 𝕋 (n + n) := Fin.append (-S₂.c) S₂.c
  let tie₁Gen : Fin S₁.m → Vec 𝕋 (n + n) := fun j =>
    Fin.append (-(S₁.G j)) fun r => S₁.G j r
  let tie₂Gen : Fin S₂.m → Vec 𝕋 (n + n) := fun j =>
    Fin.append (-(S₂.G j)) fun r => S₂.G j r
  let tieZ : Fin n → Vec 𝕋 (n + n) := fun i => Fin.append (unit i) (-(unit i))
  -- the two inequalities side by side for `β₁`, `β₂`; nothing of them for `z`
  let X : Fin ((S₁.m + S₂.m) + n) → Mat 𝕋 (S₁.k + S₂.k) (S₁.k + S₂.k) :=
    Fin.append (Fin.append (fun j => blockDiag zero (S₁.A j) fun _ _ => zero)
      (fun j => blockDiag zero (fun _ _ => zero) (S₂.A j))) fun _ _ _ => zero
  let d : Fin ((S₁.m + S₂.m) + n) → Vec 𝕋 ((n + n) + (n + n)) :=
    Fin.append (Fin.append (fun j => Fin.append (tie₁Gen j) zeroV)
      (fun j => Fin.append zeroV (tie₂Gen j))) fun i => Fin.append (tieZ i) (tieZ i)
  { k := (S₁.k + S₂.k) + ((n + n) + (n + n))
    m := (S₁.m + S₂.m) + n
    A₀ := blockDiag zero (blockDiag zero S₁.A₀ S₂.A₀)
      (diagonalBlock (Fin.append tie₁Const tie₂Const))
    A := fun l => blockDiag zero (X l) (diagonalBlock (d l))
    c := fun _ => zero
    G := Fin.append (fun _ _ => zero) unit
    I_error := Interval.origin n }

end


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.inter (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let T₁ := S₁.absorbRounding
  let T₂ := S₂.absorbRounding
  T₁.step_tieInter T₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
