module

public import CORALean.ContSet.Taylm.Float.Operations.BranchAndBound
public import CORALean.ContSet.Taylm.Float.Theorems.BnbLoopMem
public import CORALean.ContSet.Taylm.Float.Theorems.PolyBoxBoundsMem
public import CORALean.ContSet.Taylm.Float.Theorems.ReexpBoxBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.branchAndBound` brackets the polynomial

On every point of the box `X` the polynomial of the term list lies in the result.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.branchAndBound_mem (P : List (𝕋 × (Fin n → ℕ))) (X : Fin n → Interval 𝕋) (ε : 𝕋)
    (adv : Bool) (fuel : ℕ) {t : Vec ℝ n} (ht : Taylm.InBox X t) : -- --- CONCL ---
    toReal (Taylm.branchAndBound P X ε adv fuel).inf ≤
        Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.branchAndBound P X ε adv fuel).sup :=
  Taylm.bnbLoop_mem (fun B t hB => by
      -- each setting's bound of a sub-box
      cases adv
      · exact Taylm.polyBoxBounds_mem P hB
      · exact Taylm.reexpBoxBounds_mem P hB) ε ht fuel [X] fun t' h' => ⟨X, by simp, h'⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
