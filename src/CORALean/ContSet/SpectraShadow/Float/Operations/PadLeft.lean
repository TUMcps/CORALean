module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.padLeft`

A shadow put into the first `n` coordinates of a product, zero in the last `m`. Only zeros
are stored beside the stored floats, and the error box gets exact zeros there, so nothing
rounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.padLeft (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (m : ℕ) : SpectraShadow
    𝕋 (Vec 𝕋 (n + m)) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := Fin.append S.c fun _ => zero
  G := fun j => Fin.append (S.G j) fun _ : Fin m => zero
  E := ⟨Fin.append S.E.inf fun _ => zero, Fin.append S.E.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
