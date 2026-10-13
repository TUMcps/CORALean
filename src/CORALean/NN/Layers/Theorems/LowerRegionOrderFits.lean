import CORALean.NN.Layers.Operations.LowerRegionOrder
import CORALean.NN.Layers.Theorems.RegionPolyOfRelaxationFits

/-!
# Lowering the order keeps the region fitting
Each order the loop adopts is a sound relaxation's region whose error is strictly under the
tolerance, and the one it stops at is the previous fit: the result fits whenever the start
does.
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

/-- The loop's result fits `[l, u]` if the fit it starts from does. -/
theorem lowerRegionOrder_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Sound σ) (tol l u : 𝕋) :
    ∀ (k : ℕ) (cur : RegionPoly 𝕋), cur.Fits σ tol l u →
      (lowerRegionOrder F tol l u k cur).Fits σ tol l u := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
      intro cur hcur
      unfold lowerRegionOrder
      split_ifs with h
      · exact ih _ (RegionPoly.ofRelaxation_fits (hF k)
          (le_of_lt (toReal_lt_of_ltStrict h)))
      · exact hcur

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
