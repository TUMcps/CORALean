import CORALean.ContSet.Taylm.Float.Operations.BernsteinCoeffBounds
import CORALean.ContSet.Taylm.Float.Theorems.BernsteinEntryBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.BoundsProdMem
import CORALean.ContSet.Taylm.Real.Operations.BernsteinCoeff

/-!
# A Bernstein coefficient lies in its bracket

The coefficient of the exact term list the floats read as, at any multi-index, lies between the two
floats `bernsteinCoeffBounds` returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bernsteinCoeffBounds_mem (L : List (𝕋 × (Fin n → ℕ))) (N : ℕ)
    (β : Fin n → Fin (N + 1)) :
    toReal (Taylm.bernsteinCoeffBounds L N β).1
        ≤ Real.Taylm.bernsteinCoeff (L.map fun a => (toReal a.1, a.2)) N β ∧
      Real.Taylm.bernsteinCoeff (L.map fun a => (toReal a.1, a.2)) N β
        ≤ toReal (Taylm.bernsteinCoeffBounds L N β).2 := by -- --- PROOF ---
  -- each term's coefficient times its entries lies in the bracket `boundsProd` forms
  have hterm : ∀ a : 𝕋 × (Fin n → ℕ),
      toReal (Taylm.boundsProd (fun k => Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N (a.2 k) (β k))
          (List.finRange n) (a.1, a.1)).1
        ≤ toReal a.1 * ∏ k, Real.Taylm.bernsteinEntry N (a.2 k) (β k) ∧
      toReal a.1 * ∏ k, Real.Taylm.bernsteinEntry N (a.2 k) (β k)
        ≤ toReal (Taylm.boundsProd (fun k => Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N (a.2 k) (β k))
          (List.finRange n) (a.1, a.1)).2 := fun a => by
    -- the entries' brackets, through the product
    have := Taylm.boundsProd_mem (fun k => Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N (a.2 k) (β k))
      (fun k => Real.Taylm.bernsteinEntry N (a.2 k) (β k)) (List.finRange n) (a.1, a.1)
      (toReal a.1) le_rfl le_rfl fun k _ =>
        Taylm.bernsteinEntryBounds_mem N (a.2 k) (β k) (Nat.lt_succ_iff.mp (β k).2)
    rwa [← Fin.prod_univ_def] at this
  unfold Taylm.bernsteinCoeffBounds Real.Taylm.bernsteinCoeff
  constructor
  · refine le_trans (listSumDown_le _) ?_
    simp only [List.map_map]
    exact List.sum_le_sum fun a _ => (hterm a).1
  · refine le_trans ?_ (sum_le_listSumUp _)
    simp only [List.map_map]
    exact List.sum_le_sum fun a _ => (hterm a).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
