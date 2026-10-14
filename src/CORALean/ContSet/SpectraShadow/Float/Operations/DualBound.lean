module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.dualBound`

The bound a dual certificate `Y` proves along `a`: `aᵀ c + tr(A₀ Y)` for the nominal shadow, plus
the error box's largest value of `aᵀ e` (per coordinate the larger of the two corner products),
every product and sum rounded up. What it bounds is `SpectraShadow.dualCertified`'s to decide.
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

def SpectraShadow.dualBound (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (Y : Mat 𝕋 S.k S.k) : 𝕋 :=
  let nominal : 𝕋 := addUp (dotUp a S.c) (sumUp fun r => dotUp (fun j => S.A₀ r j) fun j => Y j r)
  let box : 𝕋 := sumUp fun r => maximum (mulUp (a r) (S.I_error.inf r))
      (mulUp (a r) (S.I_error.sup r))
  addUp nominal box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
