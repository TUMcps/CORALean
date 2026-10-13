import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.keepInvolvement`

How much of the constraint system a generator's coefficient appears in:
`∑ᵢ |Aᵢ e_j| + ∑ᵢ |Aeᵢ e_j|`. Zero exactly when the coefficient is unconstrained,
and then removing the generator costs the constraints nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The weight of generator `j`'s coefficient across every row of `P`. -/
noncomputable def ConZonotope.keepInvolvement (cZ : ConZonotope α) (j : Fin cZ.h) : ℝ :=
  (∑ i, |cZ.P.A i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h)|)
    + ∑ i, |cZ.P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h)|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
