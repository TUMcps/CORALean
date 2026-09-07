import CORALean.ContSet.PolyZonotope.Real.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy

/-!
# `PolyZonotope.reduceGirard`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

The two blocks are ranked as one, which is what bounds the result: `(o-1)·n` of
the concatenation are kept, so the `n` the box adds brings the total back to
`n·o`, where ranking the dependent block alone leaves `q` free to grow. The
joint ranking enters as one number, `aux_girardKeptDep`, and each block is cut
at its share of the budget by the same metric, selecting what the joint cut
selects.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `reduceGirard` below needs it
/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once.
The cap at `K` never binds and is there to keep the order bound arithmetic. -/
noncomputable def PolyZonotope.aux_girardKeptDep (pZ : PolyZonotope (Vec ℝ n)) (K : ℕ) : ℕ :=
  let rank := (Tuple.sort fun l =>
    -PolyZonotope.girardMetric (Fin.append pZ.G pZ.GI) l).symm
  min K (Finset.univ.filter fun l : Fin pZ.h =>
    (rank (Fin.castAdd pZ.q l) : ℕ) < K).card


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(pZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. Noncomputable, as ordering reals is. -/
noncomputable def PolyZonotope.reduceGirard (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  if o * n < pZ.h + pZ.q then
    let K := (o - 1) * n
    let d := pZ.aux_girardKeptDep K
    pZ.reduceBy (PolyZonotope.girardSplit (PolyZonotope.girardMetric pZ.G) d)
      (PolyZonotope.girardSplit (PolyZonotope.girardMetric pZ.GI) (K - d))
  else pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
