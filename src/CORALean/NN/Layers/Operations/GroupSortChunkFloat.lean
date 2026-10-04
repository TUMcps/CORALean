import CORALean.Global.Float.SoundFloatArithmetic

/-!
# One chunk of CORA's `nnGroupSortLayer` at float entries

`reshape(input_, [groupSize numGroups_ bSz])` puts the entries `k·g, …, k·g + g - 1` of the input in
one column; here the chunk is taken without padding, its entries as a list, at most `g`, on stored
`𝕋` values.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k`-th chunk of `g` consecutive entries of `x`, the last one possibly shorter. -/
def groupSortChunkFloat (g : ℕ) (x : Vec 𝕋 n) (k : ℕ) : List 𝕋 :=
  List.ofFn fun r : Fin (min g (n - k * g)) => x ⟨k * g + r, by have := r.2; omega⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
