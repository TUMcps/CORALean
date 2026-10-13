import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGenAll
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitIndepGenOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestGenOuter

/-!
# `splitLongestGenAll` covers the set

Every point of the set is in one of the pieces: the set itself where nothing is split, else
one of the two halves (`splitLongestGen_outer`, `splitIndepGen_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongestGenAll_cover (pZ : PolyZonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ pZ.construct) :
    ∃ T ∈ pZ.splitLongestGenAll, x ∈ T.construct := by -- --- PROOF ---
  unfold PolyZonotope.splitLongestGenAll
  dsimp only
  split
  · exact ⟨pZ, List.mem_singleton_self pZ, hx⟩
  · split
    · -- a dependent generator
      rcases PolyZonotope.splitLongestGen_outer pZ hx with h | h
      · exact ⟨_, by simp, h⟩
      · exact ⟨_, by simp, h⟩
    · -- an independent one
      rcases PolyZonotope.splitIndepGen_outer pZ _ hx with h | h
      · exact ⟨_, List.mem_cons_self, h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
