import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes

/-!
# `Ellipsoid.enclose`, over a floating-point scalar

CORA's `enclose(E, M, Eplus)` as the exact layer has it: `E2 = M * Eplus` (the float
`Ellipsoid.mtimes`, outer), then the hull `orOA` of `E` and `E2`. CORA's `or(E, E2, 'outer')`
is an SDP solver's minimum-volume ellipsoid, so the hull is an argument, owing the same
contract as over ℝ: its result contains both operands. Its minimum volume is not claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.enclose (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n) (E : Ellipsoid 𝕋 n)
    (M : Mat 𝕋 n m) (Eplus : Ellipsoid 𝕋 m) : Ellipsoid 𝕋 n :=
  let E2 := Ellipsoid.mtimes M Eplus
  orOA E E2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
