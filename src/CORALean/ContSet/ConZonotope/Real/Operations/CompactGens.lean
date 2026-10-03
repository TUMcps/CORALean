import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.compactGens`

The generators `compact_ 'zeros'` keeps: those whose column of `[G; A]` has a nonzero entry,
that is, a generator that is nonzero or that some constraint reads. A constraint here is a
row of `P`, equality or inequality, read at the coefficient's unit vector.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators that are nonzero or constrained. -/
noncomputable def ConZonotope.compactGens (cZ : ConZonotope α) : Finset (Fin cZ.h) :=
  open Classical in
  Finset.univ.filter fun j => cZ.G j ≠ 0
    ∨ (∃ i, cZ.P.A i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) ≠ 0)
    ∨ ∃ i, cZ.P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
