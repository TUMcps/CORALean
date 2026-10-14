module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

@[expose] public section

/-!
# The output of a closed-loop run lies in the output set of its reachable set

`LinearSysDT.output_outer`'s statement, with the controller's own enclosure of
its input standing in for a free `U`: `reach_outer` places the state, and
`NeuralNetwork.Sound.enclose_outer` at that same enclosure places the input the
controller produces there, which is exactly the pair `outputSet_outer` asks
for — the input set the output is read at is the enclosed one, not the
looser one `reach` itself widens through, as `NeurNetContrSysDT.Operations`
already notes at the state.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
    [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.output_outer (sys : NeurNetContrSysDT 𝕋 S n)
    (out : OutputEq 𝕋 n n r) {o : ℕ} (ho : 0 < o) (R₀ : S n) {π : Vec ℝ n → Vec ℝ n}
    (hπ : sys.contr.Sound π) {x : ℕ → Vec ℝ n}
    (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    out.eval (x k) (π (x k)) ∈ construct
      (out.outputSet (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩)
        (sys.contr.enclose (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩))) :=
  out.outputSet_outer _ _ (sys.reach_outer ho R₀ hπ traj k)
    (hπ.enclose_outer _ _ (sys.reach_outer ho R₀ hπ traj k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
