import CORALean.NN.Layers.Operations.RegionPolyOfRelaxation

/-!
# A sound relaxation's region fits when its error is within the tolerance
`PolyRelaxation.Sound` is the enclosure on every box the stored values describe, so on the
box `[l, u]` the region of the relaxation encloses `σ`, and fits once its error is under the
tolerance.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxation's region on `[l, u]` fits, given its error is at most the tolerance's. -/
theorem RegionPoly.ofRelaxation_fits {σ : ℝ → ℝ} {m : ℕ} {R : PolyRelaxation 𝕋 m}
    (hR : R.Sound σ) {tol l u : 𝕋} (h : toReal (R.error l u) ≤ toReal tol) :
    (RegionPoly.ofRelaxation R l u).Fits σ tol l u :=
  ⟨rfl, rfl, fun _ ht => hR.sound (ht.1 l rfl) (ht.2 u rfl), h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
