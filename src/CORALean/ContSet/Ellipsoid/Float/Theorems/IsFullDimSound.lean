module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsFullDim
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsFullDimIff
public import Mathlib.Topology.Algebra.Group.Pointwise
public import CORALean.ContSet.Ellipsoid.Float.Theorems.SymmOfIsSymm

@[expose] public section

/-!
# A `true` from `Ellipsoid.isFullDim` proves an interior point

Read as reals, `Q` is symmetric and positive definite (`posDef_of_pdCheck`), so the nominal
ellipsoid is that of `Q`, of rank `n`, which is a nonempty interior
(`CORALean.Real.Ellipsoid.isFullDim_iff`). Adding the error box's lower corner, a member of the
nonempty box, keeps an interior point (`subset_interior_add_left`).

## Inputs
* `E` – ellipsoid

## Hypotheses
* `h` – `isFullDim` returns `true`

## Conclusion
* `E` has nonempty interior
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isFullDim_sound {E : Ellipsoid 𝕋 n} (h : E.isFullDim = true) : -- --- CONCL ---
    (interior E.construct).Nonempty := by -- --- PROOF ---
  simp only [Ellipsoid.isFullDim, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true] at h
  obtain ⟨⟨hs, hc⟩, hbox⟩ := h
  -- `Q` is positive definite, so the nominal ellipsoid has full rank
  have hpd : (toRealMat E.Q).PosDef :=
    Ellipsoid.posDef_of_pdCheck hc (fun i j => ⟨le_rfl, le_rfl⟩) (Ellipsoid.symm_of_isSymm hs)
  have hrank : (nominal E).ellipsoid.rank = n := by
    show (nominal E).ellipsoid.Q.rank = n
    rw [Ellipsoid.nominal_of_psd hpd.posSemidef]
    have hu : IsUnit (toRealMat E.Q) := hpd.isUnit
    show (toRealMat E.Q).rank = n
    rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
  -- an interior point of the nominal ellipsoid, moved by a member of the box
  obtain ⟨x, hx⟩ := (CORALean.Real.Ellipsoid.isFullDim_iff (nominal E).ellipsoid).mpr hrank
  have he : (fun i => toReal (E.I_error.inf i)) ∈ E.I_error.construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hbox i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
