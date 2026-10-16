module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Output equations: the representation

CORA's output equation `y = C x + D u + k`, constant included, as an object of its own: an
equation from a model reads off it as written, `k` and all. `LinearSys.outputEq` and
`LinearSysDT.outputEq` read it off a system; standing alone, it pairs with a set rather than a
system, so one equation serves the sample times of a continuous system, the steps of a
discrete one and a hybrid location's enclosure alike. The noise term `F v` is not part of it:
`outputSetNoise` takes `F` and the noise set beside it, as CORA's `outputSet` takes `params.V`.

The input dimension `m` is separate from the state dimension `n`, as CORA's are.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   14-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

structure OutputEq (𝕋 : Type) (n m r : ℕ) where
  C : Mat 𝕋 r n
  D : Mat 𝕋 r m
  k : Vec 𝕋 r

/-- The output at one state and one input, which is what an output set has to
contain. Read into ℝ by the layer's scalar, as a trajectory is. -/
def OutputEq.eval (out : OutputEq 𝕋 n m r) (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ r :=
  toRealMat out.C *ᵥ x + toRealMat out.D *ᵥ u + toRealVec out.k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
