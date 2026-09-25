import CORALean.ContDynamics.OutputEq.Theorems.HoldsOfOutputSet
import CORALean.Specification.Theorems.CheckSound

/-!
# A passed check on the output set holds of every output

`holds_of_outputSet` with its hypothesis discharged by running `Specification.check` on
the set `outputSet` computed: a `true`, found by evaluation, is the specification on the
exact output of every state and input the two sets hold.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ r)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.holds_of_check [Contains ContSet (S r)] [IsDisjoint ContSet (S r)]
    (out : OutputEq 𝕋 n m r) (R : S n) (U : S m) (spec : Specification ContSet)
    {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ construct R) (hu : u ∈ construct U) :
    spec.check (out.outputSet R U) → (spec.Holds {out.eval x u}) :=
  fun h => out.holds_of_outputSet R U spec hx hu (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
