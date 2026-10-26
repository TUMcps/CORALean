module

public import CORALean.Specification.SyntaxTree.Operations.MtimesFloat
public import CORALean.Specification.SyntaxTree.Theorems.SoundSumFloat
public import CORALean.Specification.SyntaxTree.Theorems.SoundTimesFloat

@[expose] public section

/-!
# `mtimes` of sound float trees is sound

Entry `(i,j)` of `mtimesFloat` is a `sumFloat` of `timesFloat` nodes, each sound when its two
factors are, so every entry is sound when the entries of both matrices are.

## Inputs
* `m` – rows of the first matrix
* `k` – inner dimension minus one
* `p` – columns of the second matrix
* `A` – first matrix of trees
* `C` – second matrix of trees
* `i` – row index
* `j` – column index

## Hypotheses
* `hA` – every entry of the first matrix is sound
* `hC` – every entry of the second matrix is sound

## Conclusion
* the entry of the product is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}
  {B : Float.Interval (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of `mtimesFloat` of sound float trees is sound. -/
theorem SyntaxTree.isSound_mtimesFloat {m k p : ℕ}
    {A : Fin m → Fin (k + 1) → Float.SyntaxTree 𝕋 n}
    {C : Fin (k + 1) → Fin p → Float.SyntaxTree 𝕋 n}
    (hA : ∀ i l, SyntaxTree.IsSoundFloat B (A i l))
    (hC : ∀ l j, SyntaxTree.IsSoundFloat B (C l j)) (i : Fin m) (j : Fin p) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.mtimesFloat A C i j) :=
  SyntaxTree.isSound_sumFloat (SyntaxTree.isSound_timesFloat (hA i 0) (hC 0 j)) (fun u hu => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hu
    exact SyntaxTree.isSound_timesFloat (hA i l.succ) (hC l.succ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
