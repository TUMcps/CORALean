module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.tieInter`

The intersection of the two *nominal* shadows, without a computed entry: the point becomes `n`
further free variables `z`, tied to each shadow's point by the equalities `z - c₁ - G₁ β₁ = 0`
and `z - c₂ - G₂ β₂ = 0` (each as a diagonal entry and its negation, beside the two inequalities),
and the result is `z` itself, generators `[0 | I]` and centre `0`. Over ℝ the exact layer ties
the two points directly, `c₁ - c₂ + G₁ β₁ - G₂ β₂ = 0`, which needs the rounded `c₁ - c₂`; the
extra variable keeps every stored entry a stored float, its exact negation, `zero` or `one`. The
error boxes are ignored: `SpectraShadow.inter` absorbs them first.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.tieInter (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let unit : Fin n → Vec 𝕋 n := fun i r => if r = i then one else zero
  let zeroV : Vec 𝕋 (n + n) := fun _ => zero
  -- `z - c - Gβ = 0` as that expression and its negation: constants, `β` and `z` coefficients
  let tie₁Const : Vec 𝕋 (n + n) := Fin.append (fun r => neg (S₁.c r)) S₁.c
  let tie₂Const : Vec 𝕋 (n + n) := Fin.append (fun r => neg (S₂.c r)) S₂.c
  let tie₁Gen : Fin S₁.m → Vec 𝕋 (n + n) := fun j =>
    Fin.append (fun r => neg (S₁.G j r)) fun r => S₁.G j r
  let tie₂Gen : Fin S₂.m → Vec 𝕋 (n + n) := fun j =>
    Fin.append (fun r => neg (S₂.G j r)) fun r => S₂.G j r
  let tieZ : Fin n → Vec 𝕋 (n + n) := fun i => Fin.append (unit i) fun r => neg (unit i r)
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
    E := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
