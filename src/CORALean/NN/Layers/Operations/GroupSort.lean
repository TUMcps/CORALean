import CORALean.NN.Layers.Operations.GroupSortChunk

/-!
# CORA's `nnGroupSortLayer`

`evaluateNumeric`: the input is padded with `Inf` to a multiple of `groupSize`, cut into chunks
of `groupSize`, each chunk sorted ascending, and the padding cut off. The padding sorts last, so
the result in a short last chunk is that chunk's entries sorted. The layer has no enclosure in
CORA (`evaluateZonotopeBatch` throws), so this is the layer's numeric function.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Entry `i` is the `i mod g`-th smallest entry of the chunk `⌊i / g⌋`. -/
noncomputable def groupSort (g : ℕ) (x : Vec ℝ n) : Vec ℝ n := fun i =>
  ((groupSortChunk g x (i / g)).mergeSort (fun a b => decide (a ≤ b))).getD (i % g) 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
