module

public import CORALean.NN.Layers.Operations.FindRegionLeft
public import CORALean.NN.Layers.Theorems.LowerRegionOrderFits

@[expose] public section

/-!
# The left region found fits
Whatever `findRegionLeft` returns is a region `[l, u']` enclosing `σ` with error at most the
tolerance, `u'` being the right end it returns. The test that accepts a fit is `le`, whose
`true` certifies `error ≤ tol`.

## Inputs
* `σ` – activation function
* `F` – polynomial relaxations by order
* `order` – polynomial order
* `tol` – error tolerance
* `l` – left end of the uncovered domain

## Hypotheses
* `hF` – every relaxation is sound for the activation

## Conclusion
* a returned left region encloses the activation within the tolerance
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

/-- A returned left region fits `[l, u']`. -/
theorem findRegionLeft_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Sound σ) (order : ℕ) (tol l : 𝕋) : -- --- CONCL ---
    ∀ (fuel : ℕ) (ui : 𝕋) (r : RegionPoly 𝕋) (u' : 𝕋),
      findRegionLeft F order tol l fuel ui = some (r, u') → r.Fits σ tol l u' := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [findRegionLeft] at h
  | succ fuel ih =>
      intro ui r u' h
      unfold findRegionLeft at h
      dsimp only at h
      split_ifs at h with hle hlt
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact lowerRegionOrder_fits hF tol l ui order _
          (RegionPoly.ofRelaxation_fits (hF order) (SoundFloatArithmetic.toReal_le_of_le hle))
      · exact ih _ r u' h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
