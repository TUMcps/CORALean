module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.BernsteinStepMem
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinEntry

@[expose] public section

/-!
# A Bernstein entry lies in its bracket

For `j ≤ N`, `bernsteinEntry N e j` lies between the two floats `bernsteinEntryBounds` returns: its
terms lie in their brackets (`bernsteinStep_mem`), and the two sums round outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bernsteinEntryBounds_mem (N e j : ℕ) (hj : j ≤ N) :
    toReal (Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N e j).1 ≤ Real.Taylm.bernsteinEntry N e j ∧
      Real.Taylm.bernsteinEntry N e j ≤ toReal (Taylm.bernsteinEntryBounds (𝕋 := 𝕋) N e j).2
    := by -- --- PROOF ---
  have hs : ∀ i, toReal (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).1
        ≤ ((j.choose i : ℝ) / (N.choose i : ℝ)) * ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i)) ∧
      ((j.choose i : ℝ) / (N.choose i : ℝ)) * ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i))
        ≤ toReal (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).2 :=
    fun i => Taylm.bernsteinStep_mem N e j i hj
  have hsum : ∀ g : ℕ → ℝ, ((List.range (e + 1)).map g).sum = ∑ i ∈ Finset.range (e + 1), g i :=
    fun g => rfl
  unfold Taylm.bernsteinEntryBounds Real.Taylm.bernsteinEntry
  constructor
  · refine le_trans (listSumDown_le _) ?_
    rw [List.map_map, ← List.map_map (g := toReal), List.map_map, hsum]
    exact Finset.sum_le_sum fun i _ => (hs i).1
  · refine le_trans ?_ (sum_le_listSumUp _)
    rw [List.map_map, ← List.map_map (g := toReal), List.map_map, hsum]
    exact Finset.sum_le_sum fun i _ => (hs i).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
