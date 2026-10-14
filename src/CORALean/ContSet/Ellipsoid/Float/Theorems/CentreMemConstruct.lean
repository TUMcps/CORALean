module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The stored centre is a point of the ellipsoid

The stored centre, read as reals, lies in the nominal part at the zero coefficient vector, and in
the whole set once the error box holds `0`, which a box built by the operations does and an
arbitrary one need not (as for `Zonotope.centre_mem_construct`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.centre_mem_construct (E : Ellipsoid 𝕋 n)
    (h0 : ∀ i, toReal (E.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (E.I_error.sup i)) :
    toRealVec E.centre ∈ E.construct :=
  ⟨toRealVec E.centre,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨0, by simp [norm₂_zero], fun i => by
      simp [Ellipsoid.centre, toRealVec]⟩,
    0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
