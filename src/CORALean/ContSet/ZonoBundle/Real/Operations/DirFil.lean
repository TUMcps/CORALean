module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Pool
public import CORALean.ContSet.Zonotope.Real.Operations.MethCFilter
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.MinMax
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# `ZonoBundle.dirFil`: the generator filtering heuristic

The fil method of [1, Heuristic fil]: of the bundle's generators, short ones are discarded
(`methCFilter`, the length stage of method C, which the paper names), then of every `n`-subset
of what remains the one spanning the largest `|det|` is taken, the paper's smallest `Ψ`. The
filter for nearly parallel generators is not separate: a near-parallel subset has a small
determinant and loses the search. Where the best subset is singular, or fewer than `n` remain,
`Λ = I`.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The fil method [1, Heuristic fil]: the filtered pool's `n` generators of largest `|det|`. -/
noncomputable def ZonoBundle.dirFil (zB : ZonoBundle (Vec ℝ n)) : Mat ℝ n n :=
  open scoped Classical in
  let P := zB.pool                                                  -- every member's generators
  let part : Split (Fin P.h) into (Fin 0) ⊕ (Fin P.h) :=
    (Partition.split 0 P.h).reindex (finCongr (Nat.zero_add P.h).symm)  -- nothing is kept aside
  let basis := fun s : List (Fin (min (n + 8) P.h)) =>              -- the subset `s`, as columns
    (Matrix.of fun i k => ((s[k.1]?).map fun c => P.G (P.methCFilter part c) i).getD 0 : Mat ℝ n n)
  let best := (List.sublistsLen n (List.finRange _)).argmax fun s => |(basis s).det|
  let Λ := (best.map basis).getD 1                                  -- largest volume, or `I`
  if IsUnit Λ.det then Λ else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
