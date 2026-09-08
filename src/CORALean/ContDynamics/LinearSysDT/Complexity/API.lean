import CORALean.ContDynamics.LinearSysDT.Complexity.ReachError
import CORALean.ContDynamics.LinearSysDT.Complexity.ReachErrorReduced
import CORALean.ContDynamics.LinearSysDT.Complexity.ReachOrders

/-!
# How large `LinearSysDT`'s computed sets are

Generator counts, proved from the definitions. Two, and the contrast between
them is the content: `reachError_h_le` bounds the unreduced error by `k * n`,
growing with the horizon because that recursion carries every earlier box
forward without reducing, while `reachErrorReduced_h_le` holds the reduced one
at `o * n` at every horizon — so the set subtracted in `reachInnerReduced` is
described no more expensively than the run it comes off.

`reach`'s own bound is `Theorems/ReachOrderLe.lean` rather than a file here,
where it landed before this directory existed, and `Theorems/ReachBigO.lean`
reads one parameter's slice off it. `ReachOrders` is that bound at a per-step
order sequence, `o (k + 1) * n` in place of the one fixed `o * n`, and lives
here since this directory now does.

What running a step *costs* is the other kind of claim and lives in `Cost/`: a
size follows from a definition and a running cost does not, so one is proved
here and the other asserted there.
-/
