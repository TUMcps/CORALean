import CORALean.ContSet.Taylm.Float.Operations.BranchAndBound
import CORALean.ContSet.Taylm.Float.Theorems.BnbLoopMem
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoxBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.ReexpBoxBoundsMem

/-!
# `Taylm.branchAndBound` brackets the polynomial

On every point of the box `X` the polynomial of the term list lies in the result.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.branchAndBound_mem (P : List (𝕋 × (Fin n → ℕ))) (X : Fin n → 𝕋 × 𝕋) (ε : 𝕋)
    (adv : Bool) (fuel : ℕ) {t : Vec ℝ n} (ht : Taylm.InBox X t) :
    toReal (Taylm.branchAndBound P X ε adv fuel).1 ≤
        Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.branchAndBound P X ε adv fuel).2 :=
  Taylm.bnbLoop_mem (fun B t hB => by
      -- each setting's bound of a sub-box
      cases adv
      · exact Taylm.polyBoxBounds_mem P hB
      · exact Taylm.reexpBoxBounds_mem P hB) ε ht fuel [X] fun t' h' => ⟨X, by simp, h'⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
