module

public import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.projectHighDim_` over a floating-point scalar

The centre and every generator row written into the coordinates `proj` of a zero vector of
length `N`, and the error box padded with `Interval.projectHighDim_`. A coordinate outside the
range of `proj` reads `zero`; one inside reads the first source coordinate mapped to it, which
for an injective `proj` is the only one. Nothing is computed, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.projectHighDim_ (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) (proj : Fin n → Fin N) :
    Zonotope (Vec 𝕋 N) where
  h := Z.h
  c := fun j => if h : ∃ k, proj k = j then Z.c (Fin.find (fun k => proj k = j) h) else zero
  G := fun l j =>
    if h : ∃ k, proj k = j then Z.G l (Fin.find (fun k => proj k = j) h) else zero
  I_error := Z.I_error.projectHighDim_ N proj

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
