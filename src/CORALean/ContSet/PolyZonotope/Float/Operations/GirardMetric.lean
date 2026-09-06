import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# Girard's ranking metric on one generator, over a floating-point scalar

Split out of `Reduce.lean` (issue #62), no longer `aux_`: `reduceGirard` and
`reduceGirardDependent` each need it from their own file, so neither can keep
it file-local.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`, over a bare matrix
so that either block and their concatenation are ranked by this one line. Zero
on the axis-aligned generators, which a box reproduces for free. -/
def PolyZonotope.girardMetric {m : ℕ} (G : Mat 𝕋 n m) (l : Fin m) : 𝕋 :=
  subDown (sumUp fun i => absolute (G i l)) (maximumOver fun i => absolute (G i l))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
