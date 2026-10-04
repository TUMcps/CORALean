import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert

/-!
# The error box's lower corner is a member of the error set

When `inf ≤ sup` is certified entry by entry.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.corner_mem {cZ : ConZonotope 𝕋 n}
    (hE : ∀ i, le (cZ.E.inf i) (cZ.E.sup i) = true) :
    (fun i => toReal (cZ.E.inf i)) ∈ (error cZ).construct := fun i =>
  ⟨le_refl _, toReal_le_of_le (hE i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
