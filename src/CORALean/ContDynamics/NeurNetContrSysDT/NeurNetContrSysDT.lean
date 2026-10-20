module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# A neural network in the loop of a discrete-time plant: the representation

CORA's `neurNetContrSys` at a discrete-time plant [1], any `ContDynamicsDT`: the controller
reads the state and produces the first `m` inputs of the plant, `u_nn(k) = π(x(k))`, and the
plant advances by its own equation. The remaining `nExt` inputs are external, CORA's `n_ext`,
in `U_ext`; the plant receives `U_nn × U_ext` (`inputSet`), as in `NeurNetContrSys`. One
controller invocation per plant step, so a run is indexed by the step `k`. CORA's closed loop
at a `linearSysDT` drops `E`, so its reachability is for a disturbance `E` sends to `0`. The
runs are `IsTrajectory`: a run of the plant whose input at step `k` is `[π(x(k)); v(k)]`.

## References

* [1] `contDynamics/@neurNetContrSys/neurNetContrSys.m`, `aux_computeProperties`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling its first `m` inputs, the rest external, and the
sampling time `dt`: CORA's `neurNetContrSys(sys, nn, dt)`. -/
structure NeurNetContrSysDT (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamicsDT P n] where
  plant : P
  m : ℕ
  hm : m ≤ nrOfInputs plant
  contr : NeuralNetwork S n m
  dt : ℝ

/-- CORA's `n_ext`: the plant's inputs the network does not drive. -/
abbrev NeurNetContrSysDT.nExt (sys : NeurNetContrSysDT P S n) : ℕ := nrOfInputs sys.plant - sys.m

/-- The plant's input `[a; e]`: the network's output `a`, the external input `e`. -/
def NeurNetContrSysDT.input (sys : NeurNetContrSysDT P S n) (a : Vec ℝ sys.m)
    (e : Vec ℝ sys.nExt) : Vec ℝ (nrOfInputs sys.plant) :=
  joinInput sys.hm a e

/-- The plant's input set `U_nn × U_ext`. -/
def NeurNetContrSysDT.inputSet (sys : NeurNetContrSysDT P S n) (U_nn : Set (Vec ℝ sys.m))
    (U_ext : Set (Vec ℝ sys.nExt)) : Set (Vec ℝ (nrOfInputs sys.plant)) :=
  {u | ∃ a ∈ U_nn, ∃ e ∈ U_ext, u = sys.input a e}

/-- One admissible run from `R₀`: at every step the plant's input is `π` of the state with the
external input `v k` in `U_ext`, its disturbance in `W`. -/
def NeurNetContrSysDT.IsTrajectory (sys : NeurNetContrSysDT P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (R₀ : S n) (U_ext : Set (Vec ℝ sys.nExt))
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (x : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ sys.nExt) (w : ℕ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop :=
  ContDynamicsDT.IsTrajectory sys.plant (construct R₀) (sys.inputSet Set.univ U_ext) W x
    (fun k => sys.input (π (x k)) (v k)) w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
