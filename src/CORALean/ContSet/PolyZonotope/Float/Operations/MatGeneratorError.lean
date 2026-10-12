import CORALean.ContSet.Interval.Float.Interval

/-!
# The error box of a family of matrix generators

`generatorError`'s counterpart at `Mat 𝕋 n m`: entry `(i, j)` of the box is symmetric, its
half-width the sum of the generators' absolute entries at `(i, j)`, rounded up — `radius` of the
generators' `(i, ·)` rows laid out as columns. Any combination of matrices bounded entrywise by
these, with coefficients in `[-1, 1]`, lies in it (`mem_matGeneratorError`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.matGeneratorError (G : Fin h → Mat 𝕋 n m) : Interval (Mat 𝕋 n m) :=
  ⟨fun i j => neg (radius (fun j' l => G l i j') j), fun i j => radius (fun j' l => G l i j') j⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
