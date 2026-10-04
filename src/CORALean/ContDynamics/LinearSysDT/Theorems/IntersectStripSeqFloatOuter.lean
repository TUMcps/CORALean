import CORALean.ContDynamics.LinearSysDT.Operations.IntersectStripSeqFloat
import CORALean.ContSet.Zonotope.Float.Theorems.IntersectStripOuter

/-!
# The float sequential strips enclose

Every point of the zonotope that meets all the strips lies in the zonotope the sequential
strips return, whatever the gains: `Zonotope.intersectStrip_outer` once per strip. The strips are
read as real numbers at the stored values.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intersectStripSeqFloat_outer (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p)
    (Λ : Zonotope 𝕋 n → Mat 𝕋 n p) (Z : Zonotope 𝕋 n) :
    Z.construct ∩ {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (φ i)} ⊆
      (LinearSysDT.intersectStripSeqFloat C φ y Λ Z).construct := by -- --- PROOF ---
  unfold LinearSysDT.intersectStripSeqFloat
  generalize List.finRange p = l
  induction l generalizing Z with
  | nil => exact Set.inter_subset_left
  | cons i t ih =>
    intro x hx
    refine ih _ ⟨?_, hx.2⟩
    -- strip `i` alone, as a one-row strip
    refine Zonotope.intersectStrip_outer _ _ _ _ Z ⟨hx.1, fun _ => ?_⟩
    simpa [Matrix.mulVec, dotProduct, toRealMat, toRealVec] using hx.2 i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
