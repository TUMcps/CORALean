module

public import CORALean.NN.Layers.Operations.FindRegionRight
public import CORALean.NN.Layers.Theorems.RegionPolyOfRelaxationFits

@[expose] public section

/-!
# The right region found fits
Whatever `findRegionRight` returns is a region `[l', u]` enclosing `σ` with error at most the
tolerance, `l'` being the left end it returns.

## Inputs
* `σ` – activation function
* `F` – polynomial relaxations by order
* `order` – polynomial order
* `tol` – error tolerance
* `u` – right end of the uncovered domain

## Hypotheses
* `hF` – every relaxation is sound for the activation

## Conclusion
* a returned right region encloses the activation within the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A returned right region fits `[l', u]`. -/
theorem findRegionRight_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Sound σ) (order : ℕ) (tol u : 𝕋) : -- --- CONCL ---
    ∀ (fuel : ℕ) (li : 𝕋) (r : RegionPoly 𝕋) (l' : 𝕋),
      findRegionRight F order tol u fuel li = some (r, l') →
        r.Fits σ tol l' u := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [findRegionRight] at h
  | succ fuel ih =>
      intro li r l' h
      unfold findRegionRight at h
      dsimp only at h
      split_ifs at h with hle hlt
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact RegionPoly.ofRelaxation_fits (hF order) (SoundFloatArithmetic.toReal_le_of_le hle)
      · exact ih _ r l' h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
