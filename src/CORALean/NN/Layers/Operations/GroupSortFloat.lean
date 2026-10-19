module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# CORA's `nnGroupSortLayer` at float entries

`evaluateNumeric` on a vector of `𝕋`: each chunk of `groupSize` consecutive entries is sorted by
the scalar's own comparison `FloatOps.le`, and the result entry `i` is the `i mod g`-th entry of
the sorted chunk `⌊i / g⌋`. Sorting only moves entries, so no rounding is involved; what a float
can get wrong is the comparison, which is why the sortedness theorem takes `le` to be exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `k`-th chunk of `g` consecutive entries of `x`, the last one possibly shorter. -/
def aux_groupSortChunkFloat (g : ℕ) (x : Vec 𝕋 n) (k : ℕ) : List 𝕋 :=
  List.ofFn fun r : Fin (min g (n - k * g)) => x ⟨k * g + r, by have := r.2; omega⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Entry `i` is the `i mod g`-th entry of the chunk `⌊i / g⌋`, sorted ascending by `le`. -/
def groupSortFloat (g : ℕ) (x : Vec 𝕋 n) : Vec 𝕋 n := fun i =>
  ((aux_groupSortChunkFloat g x (i / g)).mergeSort FloatOps.le).getD (i % g) FloatOps.zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
