module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.absorb`

The error box made part of the shadow: the error `e` becomes `n` further free variables, kept in
the box by the diagonal constraints `e - inf ≥ 0` and `sup - e ≥ 0` beside the old inequality,
and added to the point by identity generators. Every stored entry is a stored float, its exact
negation, `zero` or `one`, so nothing rounds, and the box left over is the origin. What it is
for: an operation that must see the whole set in the inequality (an intersection) can then work
on the nominal shadow alone.
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

def SpectraShadow.absorb (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  -- the `i`-th unit vector
  let unit : Fin n → Vec 𝕋 n := fun i r => if r = i then one else zero
  -- the box constraints `e - inf ≥ 0`, `sup - e ≥ 0`: their constants and their `e` coefficients
  let boxConst : Vec 𝕋 (n + n) := Fin.append (fun r => neg (S.E.inf r)) S.E.sup
  let boxGen : Fin n → Vec 𝕋 (n + n) := fun i => Fin.append (unit i) fun r => neg (unit i r)
  -- the old matrices for the old variables, the box coefficients for the new ones
  let X : Fin (S.m + n) → Mat 𝕋 S.k S.k := Fin.append S.A fun _ _ _ => zero
  let d : Fin (S.m + n) → Vec 𝕋 (n + n) := Fin.append (fun _ _ => zero) boxGen
  { k := S.k + (n + n)
    m := S.m + n
    A₀ := blockDiag zero S.A₀ (diagonalBlock boxConst)
    A := fun l => blockDiag zero (X l) (diagonalBlock (d l))
    c := S.c
    G := Fin.append S.G unit
    E := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
