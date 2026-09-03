import CORALean.ContSet.ContSet.ContSet

/-!
# Output equations: the representation

CORA's output equation `y = C x + D u + k`, without the constant and as an
object of its own rather than a field of a system.

Its own object, because no operation on a system reads it and one of them cannot
carry it: `reach` never sees `C`, and `LinearSys.discretize` hands `LinearSysDT`
an input set of *state contributions* over a step — `inputSolution`, not `u` —
so a `D` stored on the discrete system would multiply the wrong thing. Paired
with a set instead, one equation serves the sample times of a continuous system,
the steps of a discrete one and a hybrid location's enclosure alike, reading `u`
from the input set the run was actually described by.

No constant. A constant output offset is the one part of the equation a caller
can undo without loss: `C x + D u + k ∈ Y` is `C x + D u ∈ Y - k`, so it folds
into the specification the way `c` folds into the input set, translation being
invertible where `C` is not. Carrying it would mean absorbing a point, which
here is `OfInterval` — the one conversion class that differs between the two
arithmetic layers — and so would cost the output set a float twin for a
subtraction the caller does once.

The input dimension `m` is separate from the state dimension `n`, which
`LinearSys` and `LinearSysDT` are not: their input enters in state coordinates,
so they instantiate `m := n`. `D` is therefore feedthrough of the input *as it
reaches the state*, and CORA's `D u` is recovered from it only when `B` is
invertible — which is the one thing folding `B` into the input set does cost.
Unfolding `B` would change those systems and not this file.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Scalar

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]

structure OutputEq (𝕋 : Type) (n m r : ℕ) where
  C : Mat 𝕋 r n
  D : Mat 𝕋 r m

/-- The output at one state and one input, which is what an output set has to
contain. Read into ℝ by the layer's scalar, as a trajectory is. -/
def OutputEq.eval (out : OutputEq 𝕋 n m r) (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ r :=
  toRealMat out.C *ᵥ x + toRealMat out.D *ᵥ u

end CORALean.Real
