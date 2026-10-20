module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsOuterFactor
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PsdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.SymmOfIsSymm

@[expose] public section

/-!
# A certified factor covers the shape matrix

`isOuterFactor Q G` brackets each entry of `G Gᵀ - Q` between a rounded-down and a rounded-up
evaluation, and the real matrix lies in that bracket and is symmetric once `Q` is
(`posSemidef_of_psdCheck` with the zero factor).

## Inputs
* `Q` – shape matrix
* `G` – factor

## Hypotheses
* `h` – `isOuterFactor` returns `true`

## Conclusion
* `G Gᵀ - Q` is positive semi-definite
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed `isOuterFactor` makes `G Gᵀ - Q`, read as reals, positive semi-definite. -/
theorem Ellipsoid.posSemidef_of_isOuterFactor {Q G : Mat 𝕋 n n}
    (h : Ellipsoid.isOuterFactor Q G = true) : -- --- CONCL ---
    (toRealMat G * (toRealMat G)ᵀ - toRealMat Q).PosSemidef := by -- --- PROOF ---
  simp only [Ellipsoid.isOuterFactor, Bool.and_eq_true] at h
  obtain ⟨hs, hc⟩ := h
  -- each entry is the real dot product of two rows, less `Q`'s entry
  have he : ∀ i j, (toRealMat G * (toRealMat G)ᵀ - toRealMat Q) i j
      = ∑ k, toReal (G i k) * toReal (G j k) - toReal (Q i j) := fun i j => by
    simp [Matrix.mul_apply, toRealMat]
  refine Ellipsoid.posSemidef_of_psdCheck hc (fun i j => ⟨?_, ?_⟩) (fun i j => ?_)
  · rw [he]
    exact (subDown_le_sub _ _).trans (by linarith [dotDown_le (G i) (G j)])
  · rw [he]
    exact le_trans (by linarith [le_dotUp (G i) (G j)]) (sub_le_subUp _ _)
  · rw [he, he, Ellipsoid.symm_of_isSymm hs i j]
    simp only [mul_comm]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
