module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard

@[expose] public section

/-!
# `PolyZonotope.reduceGirardCost`

Asserted, not proved, by reading `Operations/ReduceGirard.lean`. Girard's
metric on one generator is `n` absolute values and `n - 1` additions for `‖g‖₁`,
`n` more and `n` comparisons for the `max` fold, and one negation for the
descending sort key: at most `4 * n + 2` each, as in `Zonotope`'s own file. It
is evaluated on the concatenation for the joint rank and again on each block for
its split, so twice over `h + q` bounds it.

Three sorts follow — the joint one and one per block — each bounded by `Cost.sort` at the joint
width; `aux_girardKeptDep` then counts the dependent ranks, `h` comparisons and a `min`.

No order argument: below `o * n` the operation is the identity and costs
nothing, and above it the absorbed blocks are `h` and `q` wide at worst either
way, so this bounds every `o` at once.

`reduceBy` is charged at the most it can keep and absorb and writes its own result.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduceGirard` costs at `Vec ℝ n` over `p` factors on `h` dependent and `q`
independent generators: the metrics, the sorts, the count, and the absorption at most `h` and `q`
kept and `h` and `q` absorbed. -/
def PolyZonotope.reduceGirardCost (n p h q : ℕ) : Cost :=
  ⟨(h + q) * (8 * n + 4) + (h + q) + 1⟩ + 3 • Cost.sort (h + q)
    + PolyZonotope.reduceByCost n p h q h q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
