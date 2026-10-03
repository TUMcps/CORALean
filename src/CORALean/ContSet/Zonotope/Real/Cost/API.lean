import CORALean.ContSet.Zonotope.Real.Cost.Plus
import CORALean.ContSet.Zonotope.Real.Cost.LinComb
import CORALean.ContSet.Zonotope.Real.Cost.Mtimes
import CORALean.ContSet.Zonotope.Real.Cost.Map
import CORALean.ContSet.Zonotope.Real.Cost.ReduceBy
import CORALean.ContSet.Zonotope.Real.Cost.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearch
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearchBigO
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearchFilteredBigO

/-!
# What running `Zonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation. Every one of them is **asserted**: read off the operation's
definition by hand and believed on that reading, since a Lean `def` says what
is computed and never what computing it costs. None is `rfl` against anything.

`Complexity/` is the other directory and the other kind of claim — how large a
*result* is, which is a theorem, proved. A reader can tell which they are
looking at three ways over: the directory, the `Cost`-valued `def` rather than
a `theorem` about `.h`, and the `…Cost` name.

Each count is an upper bound and each is monotone in the operand sizes it takes
— `mtimesCost_mono`, `reduceByCost_mono`, `reduceGirardCost_mono` — which is
what lets a caller substitute a bound on a size for the size, and so what makes
`LinearSysDT.reachCost_le` assemble out of these plus `Complexity/`'s sizes.

`mapCost` prices a general linear map at what one application costs, a
parameter no caller here fixes; `mtimesCost` is the same shape at
`Cost.matVec m n` but stays its own `def`, `M *ᵥ ·`'s price not needing one.
-/
