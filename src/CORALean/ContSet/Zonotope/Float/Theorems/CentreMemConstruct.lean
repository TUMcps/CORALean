module

public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The stored centre is a point of the zonotope

`Recentre.centre` reads the stored centre as reals. It lies in the nominal part
at the zero coefficients, and in the whole set once the error box holds `0`,
which a box built by the operations does and an arbitrary one need not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.centre_mem_construct (Z : Zonotope (Vec 𝕋 n))
    (h0 : ∀ i, toReal (Z.E.inf i) ≤ 0 ∧ 0 ≤ toReal (Z.E.sup i)) :
    toRealVec Z.c ∈ Z.construct :=
  ⟨toRealVec Z.c,
    Zonotope.mem_nominalSet_iff.mpr ⟨0, fun j => by simp, fun i => by simp [toRealVec]⟩,
    0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
