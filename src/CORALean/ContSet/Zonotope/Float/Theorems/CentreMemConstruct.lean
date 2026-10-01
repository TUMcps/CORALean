import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# The stored centre is a point of the zonotope

`Recentre.centre` reads the stored centre as reals. It lies in the nominal part
at the zero coefficients, and in the whole set once the error box holds `0`,
which a box built by the operations does and an arbitrary one need not.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.centre_mem_construct (Z : Zonotope 𝕋 n)
    (h0 : ∀ i, toReal (Z.E.inf i) ≤ 0 ∧ 0 ≤ toReal (Z.E.sup i)) :
    toRealVec Z.c ∈ Z.construct :=
  ⟨toRealVec Z.c,
    Zonotope.mem_nominalSet_iff.mpr ⟨0, fun j => by simp, fun i => by simp [toRealVec]⟩,
    0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
