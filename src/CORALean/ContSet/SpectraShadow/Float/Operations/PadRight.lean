module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.padRight`

A shadow put into the last `m` coordinates of a product, zero in the first `n`. Only zeros
are stored beside the stored floats, and the error box gets exact zeros there, so nothing
rounds.

## Inputs
* `n` – natural number
* `S` – spectrahedral shadow

## Output
* `S` in the last `m` coordinates of the product, zero in the first `n`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.padRight (n : ℕ) (S : SpectraShadow 𝕋 (Vec 𝕋 m)) : SpectraShadow
    𝕋 (Vec 𝕋 (n + m)) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := Fin.append (fun _ : Fin n => zero) S.c
  G := fun j => Fin.append (fun _ : Fin n => zero) (S.G j)
  I_error := ⟨Fin.append (fun _ : Fin n => zero) S.I_error.inf, Fin.append (fun _ : Fin n => zero)
      S.I_error.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
