import CORALean.ContDynamics.OutputEq.Operations

/-!
# `outputSet` contains the output of every state-input pair it was given

The guarantee that makes an output set usable, and it is `Layer.linear`'s
argument with the bias replaced by a second `mtimes`: the two terms are enclosed
separately and `plus` puts them back together.

Stated at a single state and input rather than along a run, which is what keeps
it independent of the system: the caller supplies `x ∈ R` from whatever produced
`R` — a discrete recursion, a sampled flow, a hybrid invariant — and `u ∈ U`
from the run's own input set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.outputSet_outer (out : OutputEq 𝕋 n m r) (R : S n) (U : S m)
    {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ construct R) (hu : u ∈ construct U) :
    out.eval x u ∈ construct (out.outputSet R U) :=
  plus_outer _ _ (Set.add_mem_add
    (mtimes_outer out.C R (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (mtimes_outer out.D U (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hu))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
