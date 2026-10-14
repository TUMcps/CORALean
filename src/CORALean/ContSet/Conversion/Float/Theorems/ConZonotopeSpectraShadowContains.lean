module

public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopePosSemidefSpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePosSemidefSpectraShadow

@[expose] public section

/-!
# A constrained zonotope as a spectrahedral shadow, over a floating-point scalar

CORA's `@conZonotope/spectraShadow`: the box inequalities `1 ± βⱼ ≥ 0` and the constraint rows
along one block-diagonal matrix. The first block is the zonotope's own and the second the
coefficient polytope's, as for the exact layer, with the stored `zero` between them; the centre,
generators and error box are carried over. Nothing rounds, so nothing is paid. The shadow
contains the constrained zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.spectraShadow_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.spectraShadow.construct := by -- --- PROOF ---
  -- the box is carried over, so only the nominal parts are compared
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hP, hx'⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  refine SpectraShadow.mem_nominalSet_iff.mpr ⟨β, ?_, hx'⟩
  -- both blocks are positive semidefinite at `β`
  have h := (posSemidef_blockDiag_iff _ _).mpr ⟨Zonotope.posSemidef_spectraShadow cZ.zonotope β hβ,
    HPolytope.posSemidef_spectraShadow cZ.P hP⟩
  -- the stored block-diagonal matrices read as the block-diagonal of what the blocks read as
  change (toRealMat (blockDiag FloatOps.zero cZ.zonotope.spectraShadow.A₀ cZ.P.spectraShadow.A₀)
    + ∑ j : Fin cZ.h, β j • toRealMat (blockDiag FloatOps.zero (cZ.zonotope.spectraShadow.A j)
      (cZ.P.spectraShadow.A j))).PosSemidef
  simp only [SpectraShadow.toRealMat_blockDiag, ← blockDiag_smul]
  rw [← blockDiag_sum, ← blockDiag_add]
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
