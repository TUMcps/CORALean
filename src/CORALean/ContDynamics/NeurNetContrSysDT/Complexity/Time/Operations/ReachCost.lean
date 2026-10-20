module

public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.ReachCost
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.NN.Complexity.Time.Operations.EncloseCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `NeurNetContrSysDT.reachCost`

What running `reach` costs, assembled: `Operations.lean` alternates one call to `enclose` with one
step of `LinearSysDT.reach`, so a step here is one `encloseCost`, the `mtimes` by `B_nn`, the
`mtimes` by `B_ext` of the external inputs `U_ext` and the two `plus`es (with `c`) that make the
input set, and the `mtimes`, `plus` and `reduce` the plant's step unfolds to. `LC` is the per-layer
bound `encloseCost` takes. At `𝒵` and `𝕋 = ℝ`, as `LinearSysDT.reachCost` is. `reachStepBound` is
`encloseCost`, fixed for the whole run, plus the input map's two costs and
`LinearSysDT.reachStepBound` at a caller-supplied bound `hEnc` on the enclosure's generator count.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `LC` – per-layer cost bound

## Hypotheses
* `ho` – order positive

## Output
* the cost of `reach` after each number of steps
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` costs over `k` steps at `𝒵`, at a per-layer bound `LC`: per
step one `NeuralNetwork.encloseCost`, the input map's two `mtimes` and two `plus`es (the second
adding the point `c`, without generators), and the plant's `mtimes`, `plus` and `reduce`. -/
noncomputable def NeurNetContrSysDT.reachCost (sys : NeurNetContrSysDT (LinearSysDT ℝ n) 𝒵 n)
    (U_ext : Zonotope (Vec ℝ sys.nExt)) (o : ℕ) (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost) : ℕ → Cost
  | 0 => 0
  | k + 1 =>
      -- the set reached so far, and what the controller's enclosure of it carries
      let hR := (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩).h
      let hE := (sys.contr.enclose (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩)).h
      sys.reachCost U_ext o ho R₀ LC k
        + (NeuralNetwork.encloseCost LC sys.contr
            + (Zonotope.mtimesCost n sys.m hE + Zonotope.plusCost n hE U_ext.h)
            + (Zonotope.mtimesCost n sys.nExt U_ext.h + Zonotope.plusCost n (hE + U_ext.h) 0)
            + (Zonotope.mtimesCost n n hR + Zonotope.plusCost n hR (hE + U_ext.h)
                + Zonotope.reduceGirardCost n (hR + (hE + U_ext.h))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
