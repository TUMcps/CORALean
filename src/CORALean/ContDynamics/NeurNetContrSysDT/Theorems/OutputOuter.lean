import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

/-!
# The output of a closed-loop run lies in the output set of its reachable set

`LinearSysDT.output_outer`'s statement, with the controller's own enclosure of
its input standing in for a free `U`: `reach_outer` places the state, and
`NeuralNetwork.enclose_outer` at that same enclosure places the input the
controller produces there, which is exactly the pair `outputSet_outer` asks
for — the input set the output is read at is the enclosed one, not the
looser one `reach` itself widens through, as `NeurNetContrSysDT.Operations`
already notes at the state.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.output_outer (sys : NeurNetContrSysDT 𝕋 S n)
    (out : OutputEq 𝕋 n n r) (o : ℕ) (R₀ : S n) {x : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ x) (k : ℕ) :
    out.eval (x k) (sys.contr.eval (x k)) ∈ construct
      (out.outputSet (sys.reach o R₀ k) (sys.contr.enclose (sys.reach o R₀ k))) :=
  out.outputSet_outer _ _ (sys.reach_outer o R₀ traj k)
    (sys.contr.enclose_outer _ _ (sys.reach_outer o R₀ traj k))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
