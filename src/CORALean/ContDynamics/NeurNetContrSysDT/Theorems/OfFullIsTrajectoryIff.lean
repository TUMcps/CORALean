module

public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Basic

@[expose] public section

/-!
# With no external input, the loop is the one in which the network drives every input

`ofFull plant contr` has `m = nrOfInputs plant`, so `nExt = 0` and the plant's input is the
network's output alone (`input a e = a`). Its `IsTrajectory`, for any nonempty `U_ext` (a set of
`Vec ℝ 0`s, which all coincide), is a run of the plant from `R₀` under the input `π(x k)` at every
step, in the plant's whole input set: the statement of the closed loop before external inputs were
modelled.

## Inputs
* `plant` – plant
* `contr` – controller network
* `dt` – sampling time
* `π` – controller function
* `R₀` – initial set
* `U_ext` – external input set
* `W` – disturbance set
* `x` – states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `hU` – external input set nonempty

## Conclusion
* a loop trajectory is a plant trajectory driven by the controller
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With `m = M`, `[a; e]` is `a`. -/
theorem NeurNetContrSysDT.aux_joinInput_full {M : ℕ} (a : Vec ℝ M) (e : Vec ℝ (M - M)) :
    joinInput (le_refl M) a e = a := by
  funext i
  simp [joinInput, i.isLt]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.ofFull_isTrajectory_iff (plant : P)
    (contr : NeuralNetwork S n (nrOfInputs plant)) (dt : ℝ)
    {π : Vec ℝ n → Vec ℝ (nrOfInputs plant)} {R₀ : S n}
    {U_ext : Set (Vec ℝ (NeurNetContrSysDT.ofFull plant contr dt).nExt)} (hU : U_ext.Nonempty)
    {W : Set (Vec ℝ (nrOfDisturbances plant))} {x : ℕ → Vec ℝ n}
    {v : ℕ → Vec ℝ (NeurNetContrSysDT.ofFull plant contr dt).nExt}
    {w : ℕ → Vec ℝ (nrOfDisturbances plant)} : -- --- CONCL ---
    (NeurNetContrSysDT.ofFull plant contr dt).IsTrajectory π R₀ U_ext W x v w ↔
      ContDynamicsDT.IsTrajectory plant (construct R₀) Set.univ W x (fun k => π (x k))
        w := by -- --- PROOF ---
  -- the plant's input is the network's output, and its input set everything
  have hin : ∀ a e, (NeurNetContrSysDT.ofFull plant contr dt).input a e = a := fun a e =>
    NeurNetContrSysDT.aux_joinInput_full a e
  have hset : (NeurNetContrSysDT.ofFull plant contr dt).inputSet Set.univ U_ext = Set.univ := by
    obtain ⟨e₀, he₀⟩ := hU
    ext u
    exact ⟨fun _ => trivial, fun _ => ⟨u, trivial, e₀, he₀, (hin u e₀).symm⟩⟩
  unfold NeurNetContrSysDT.IsTrajectory
  simp only [hin, hset]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
