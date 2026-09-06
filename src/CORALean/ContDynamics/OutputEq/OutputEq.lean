import CORALean.ContSet.ContSet.ContSet

/-!
# Output equations: the representation

CORA's output equation `y = C x + D u + k`, without the constant and as an object
of its own, because no operation on a system reads it and one of them cannot
carry it: `LinearSys.discretize` hands `LinearSysDT` an input set of *state
contributions* over a step, so a `D` stored there would multiply the wrong thing.
Paired with a set instead, one equation serves the sample times of a continuous
system, the steps of a discrete one and a hybrid location's enclosure alike.

No constant. `C x + D u + k ∈ Y` is `C x + D u ∈ Y - k`, so an offset folds into
the specification the way `c` folds into the input set. Carrying it would mean
absorbing a point, which here is `OfInterval` — the one conversion class that
differs between the arithmetic layers — so the output set would owe a float twin
for a subtraction the caller does once.

The input dimension `m` is separate from the state dimension `n`, which
`LinearSys` and `LinearSysDT` are not, their input entering in state coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Scalar

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

structure OutputEq (𝕋 : Type) (n m r : ℕ) where
  C : Mat 𝕋 r n
  D : Mat 𝕋 r m

/-- The output at one state and one input, which is what an output set has to
contain. Read into ℝ by the layer's scalar, as a trajectory is. -/
def OutputEq.eval (out : OutputEq 𝕋 n m r) (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ r :=
  toRealMat out.C *ᵥ x + toRealMat out.D *ᵥ u

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
