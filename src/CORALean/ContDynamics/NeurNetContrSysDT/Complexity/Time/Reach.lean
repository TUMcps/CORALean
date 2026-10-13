import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.NN.Complexity.Time.Enclose

/-!
# `NeurNetContrSysDT.reachCost`

What running `reach` costs, assembled: `Operations.lean` alternates one call to
`enclose` with one step of `LinearSysDT.reach`, so a step here is one
`encloseCost` plus the `mtimes`, `plus` and `reduce` that step unfolds to — the
same three `Zonotope` costs `LinearSysDT.reachCost` uses, at the sizes the
alternation itself carries. `LC` is the per-layer bound `encloseCost` takes.

At `𝒵` and `𝕋 = ℝ`, as `LinearSysDT.reachCost` is: `plus` and `reduce` cost what
a representation makes them cost, so a cost is stated where the instance is.

`reachStepBound` is `encloseCost`, fixed for the whole run since `sys.contr`
never changes, plus `LinearSysDT.reachStepBound` at a caller-supplied bound
`hEnc` on the enclosure's own generator count — a size no `Complexity/Space/` fact
gives, an activation layer's relaxation being free to grow it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` costs over `k` steps at `𝒵`, at a per-layer bound `LC`: per
step one `NeuralNetwork.encloseCost`, one `mtimes`, one `plus`, one `reduce`. -/
noncomputable def NeurNetContrSysDT.reachCost (sys : NeurNetContrSysDT ℝ 𝒵 n) (o : ℕ) (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost) : ℕ → Cost
  | 0 => 0
  | k + 1 =>
      sys.reachCost o ho R₀ LC k
        + (NeuralNetwork.encloseCost LC sys.contr
            + (Zonotope.mtimesCost n n (sys.reach (S := 𝒵) ⟨R₀, 0, k⟩ ⟨o, ho⟩).h
                + Zonotope.plusCost n
                + Zonotope.reduceGirardCost n
                    ((sys.reach (S := 𝒵) ⟨R₀, 0, k⟩ ⟨o, ho⟩).h
                      + (sys.contr.enclose (sys.reach (S := 𝒵) ⟨R₀, 0, k⟩ ⟨o, ho⟩)).h)))

/-- The same costs at a step's worst case: `o * n` generators reaching the
`mtimes`, and `hEnc` a bound on what the controller's enclosure carries into
the `reduce`. -/
def NeurNetContrSysDT.reachStepBound (sys : NeurNetContrSysDT ℝ 𝒵 n) (o hEnc : ℕ)
    (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost) : Cost :=
  NeuralNetwork.encloseCost LC sys.contr + LinearSysDT.reachStepBound n hEnc o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
