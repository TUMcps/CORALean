module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The stored center is a point of the ellipsoid

The stored center, read as reals, lies in the nominal part at the zero coefficient vector, and in
the whole set once the error box holds `0`, which a box built by the operations does and an
arbitrary one need not (as for `Zonotope.center_mem_construct`).

## Inputs
* `E` – ellipsoid

## Hypotheses
* `h0` – error box contains the origin

## Conclusion
* the stored center lies in `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.center_mem_construct (E : Ellipsoid 𝕋 n)
    (h0 : ∀ i, toReal (E.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (E.I_error.sup i)) :
    toRealVec E.center ∈ E.construct :=
  ⟨toRealVec E.center,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨0, by simp [norm₂_zero], by
      rw [Matrix.mulVec_zero, add_zero]
      rfl⟩,
    0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
