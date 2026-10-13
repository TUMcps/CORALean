module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.mask`: keep the entries a pattern selects, zero the rest

The shared definition of `tril` and `triu`: CORA applies MATLAB's `tril`/`triu` to `I.inf` and
`I.sup`, which keeps the entries of the pattern and sets the others to `0`. The box that results has
the point `0` at every entry outside the pattern.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mask (keep : Fin m → Fin n → Prop) [∀ i j, Decidable (keep i j)]
    (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ m n) where
  inf := fun i j => if keep i j then I.inf i j else 0
  sup := fun i j => if keep i j then I.sup i j else 0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
