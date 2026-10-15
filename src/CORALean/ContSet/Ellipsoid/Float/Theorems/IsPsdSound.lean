module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PsdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.SymmOfIsSymm

@[expose] public section

/-!
# A certified shape matrix is positive semi-definite

`isPsd Q` checks the floats symmetric (each pair `le` both ways, so equal as reals) and the
residual of the proposed factor diagonally dominant on the point interval of `Q`, where `Q` read
as reals is the one symmetric matrix (`posSemidef_of_psdCheck`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed `isPsd` makes the stored matrix, read as reals, positive semi-definite. -/
theorem Ellipsoid.posSemidef_of_isPsd {Q : Mat 𝕋 n n} (h : Ellipsoid.isPsd Q = true) :
    (toRealMat Q).PosSemidef := by
  simp only [Ellipsoid.isPsd, Bool.and_eq_true] at h
  obtain ⟨hs, hc⟩ := h
  exact Ellipsoid.posSemidef_of_psdCheck hc (fun i j => ⟨le_rfl, le_rfl⟩)
    (Ellipsoid.symm_of_isSymm hs)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
