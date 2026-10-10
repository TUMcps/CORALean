import CORALean.ContSet.ConZonotope.Float.Operations.CentreHi
import CORALean.ContSet.ConZonotope.Float.Operations.CentreLo

/-!
# `ConZonotope.centreLo` and `centreHi` bracket `c + G β₀`

The two ends are a rounded-down and a rounded-up evaluation of the same expression.
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

theorem ConZonotope.centre_between (cZ : ConZonotope 𝕋 n) (β₀ : Vec 𝕋 cZ.h) (i : Fin n) :
    toReal (cZ.centreLo β₀ i) ≤ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)
      ∧ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)
        ≤ toReal (cZ.centreHi β₀ i) := by -- --- PROOF ---
  have h1 := addDown_le_add (cZ.c i) (dotDown (fun j => cZ.G j i) β₀)
  have h2 := add_le_addUp (cZ.c i) (dotUp (fun j => cZ.G j i) β₀)
  have h3 := dotDown_le (fun j => cZ.G j i) β₀
  have h4 := le_dotUp (fun j => cZ.G j i) β₀
  exact ⟨by simp only [ConZonotope.centreLo]; linarith,
    by simp only [ConZonotope.centreHi]; linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
