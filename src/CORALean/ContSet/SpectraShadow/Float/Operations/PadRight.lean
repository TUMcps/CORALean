import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

/-!
# `SpectraShadow.padRight`

A shadow put into the last `m` coordinates of a product, zero in the first `n`. Only zeros
are stored beside the stored floats, and the error box gets exact zeros there, so nothing
rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.padRight (n : ℕ) (S : SpectraShadow 𝕋 m) : SpectraShadow 𝕋 (n + m) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := Fin.append (fun _ : Fin n => zero) S.c
  G := fun i j => Fin.append (fun _ : Fin n => zero) (fun i' => S.G i' j) i
  E := ⟨Fin.append (fun _ : Fin n => zero) S.E.inf, Fin.append (fun _ : Fin n => zero) S.E.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
