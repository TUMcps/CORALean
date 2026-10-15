module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.mtimes`

CORA's `@spectraShadow/mtimes`: the image under a matrix `M`. Over ℝ the generators are
`M *ᵥ Gⱼ`, but a float `M * G` rounds, and the rounding multiplies a variable `β` that nothing
bounds, so no error box holds it. The image is instead taken without computing a product of two
stored matrices: the point `z = c + Gβ` becomes `p` further free variables, tied to the old
ones by the equalities `zᵢ = cᵢ + Σⱼ Gᵢⱼ βⱼ` (two diagonal entries each, `d ≥ 0` and `-d ≥ 0`,
whose entries are stored floats or their exact negations), and the result is `M z` with
generators `[0 | M]`. No entry is computed, so the nominal shadow is exact; only the error box
is multiplied, by `Interval.mtimes`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.mtimes (M : Mat 𝕋 m n) (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow
    𝕋 (Vec 𝕋 m) :=
  -- the equalities `zᵢ - cᵢ - Σⱼ Gᵢⱼ βⱼ = 0`, as that expression and its negation, per `i`
  let constraintConst : Vec 𝕋 (n + n) := Fin.append (-S.c) S.c
  let constraintGen : Fin S.m → Vec 𝕋 (n + n) := fun j =>
    Fin.append (-(S.G j)) (fun i => S.G j i)
  let constraintPoint : Fin n → Vec 𝕋 (n + n) := fun i =>
    Fin.append (fun r => if r = i then one else zero) (fun r => if r = i then neg one else zero)
  { k := S.k + (n + n)
    m := S.m + n
    A₀ := blockDiag zero S.A₀ (diagonalBlock constraintConst)
    A := Fin.append (fun j => blockDiag zero (S.A j) (diagonalBlock (constraintGen j)))
      (fun i => blockDiag zero (fun _ _ => zero) (diagonalBlock (constraintPoint i)))
    c := fun _ => zero
    G := fun l r => Fin.append (fun _ : Fin S.m => zero) (fun i => M r i) l
    I_error := Interval.mtimes M S.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
