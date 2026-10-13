import CORALean.ContSet.Interval.Float.Operations.Empty
import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet

/-!
# `Interval.projectHighDim_`

The box placed into the coordinates `proj` of `𝕋ᴺ`, every other coordinate `zero`; a box certified
empty stays empty. The index of a coordinate is found by `Fin.find`, which `proj` makes unique
when injective.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.projectHighDim_ (I : Interval (Vec 𝕋 m)) (N : ℕ) (proj : Fin m → Fin N) :
    Interval (Vec 𝕋 N) :=
  if I.representsa_emptySet = true then Interval.empty N
  else
    { inf := fun j =>
        if h : ∃ k, proj k = j then I.inf (Fin.find (fun k => proj k = j) h) else zero
      sup := fun j =>
        if h : ∃ k, proj k = j then I.sup (Fin.find (fun k => proj k = j) h) else zero }


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
