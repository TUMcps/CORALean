module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.AugmentNonlin
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.JoinInputInj
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# At a nonlinear plant, a control period is a run of the augmented system

CORA's `aux_computeProperties` at a `nonlinearSys` ([1, Alg. 2]), checked: a run of the plant
`ẋ = f(x, u)` on
`[0, τ]` under the input `[a; v(t)]`, the network's held output `a` and an external input `v` in
`U_ext`, is with `a` appended to it a Carathéodory run of `augmentNonlin`,
`ż = [f(z₁, [z₂; e]); 0]`, under the input `v`: the field is the plant's under the zero-padding
map `y ↦ [y; 0]`, which commutes with the integral.

## Inputs
* `sys` – closed-loop system
* `τ` – period length
* `U_ext` – external input set
* `W` – disturbance set
* `x` – plant states
* `a` – held network output
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `traj` – plant trajectory under the held and external inputs

## Conclusion
* the external input stays in `U_ext`, and the plant run with the held output appended is a run
  of the augmented system from any set holding its start

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {n M : ℕ} {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero-padding `y ↦ [y; 0]` as a continuous linear map. -/
private noncomputable def aux_pad (n m : ℕ) : Vec ℝ n →L[ℝ] Vec ℝ (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.append y (fun _ : Fin m => (0 : ℝ))
      map_add' := fun y z => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      map_smul' := fun c y => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp }

/-- The field of the augmented system at `[x; a]` is the plant's, padded. -/
private theorem NeurNetContrSys.aux_augmentNonlin_f (sys : NeurNetContrSys (NonlinearSys n M) S n)
    (x : Vec ℝ n) (a : Vec ℝ sys.m) (e : Vec ℝ sys.nExt) :
    sys.augmentNonlin.f (Fin.append x a) e =
      aux_pad n sys.m (sys.plant.f x (sys.input a e)) := by
  simp [NeurNetContrSys.augmentNonlin, aux_pad, NeurNetContrSys.input]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the nonlinear plant on `[0, τ]` under the input `[a; v(t)]`, `v` in `U_ext`, is with
`a` appended a run of `augmentNonlin` under the input `v` from any set holding its start. -/
theorem NeurNetContrSys.augmentNonlin_flow (sys : NeurNetContrSys (NonlinearSys n M) S n) {τ : ℝ}
    {U_ext : Set (Vec ℝ sys.nExt)} {W : Set (Vec ℝ (ContDynamics.nrOfDisturbances sys.plant))}
    {x : ℝ → Vec ℝ n} {a : Vec ℝ sys.m} {v : ℝ → Vec ℝ sys.nExt}
    {w : ℝ → Vec ℝ (ContDynamics.nrOfDisturbances sys.plant)}
    (traj : ContDynamics.IsTrajectory sys.plant (Set.Icc 0 τ) Set.univ (sys.inputSet {a} U_ext) W x
      (fun t => sys.input a (v t)) w) : -- --- CONCL ---
    (∀ t ∈ Set.Icc 0 τ, v t ∈ U_ext) ∧ ∀ R₀ : Set (Vec ℝ (n + sys.m)),
      Fin.append (x 0) a ∈ R₀ →
        sys.augmentNonlin.IsTrajectory (S := ExactSet) (Set.Icc 0 τ) R₀ U_ext
          (fun t => Fin.append (x t) a) v (fun _ => fun i => i.elim0) := by -- --- PROOF ---
  obtain ⟨tr, -⟩ := traj
  -- the external input lies in `U_ext`
  have hv : ∀ t ∈ Set.Icc 0 τ, v t ∈ U_ext := by
    intro t ht
    obtain ⟨a', _, e, he, heq⟩ := tr.input t ht
    rw [(joinInput_inj sys.hm heq).2]
    exact he
  refine ⟨hv, fun R₀ h0 => ?_⟩
  -- the field along the run, the plant's padded
  have hf : (fun t => sys.augmentNonlin.f (Fin.append (x t) a) (v t)) =
      fun t => aux_pad n sys.m (sys.plant.f (x t) (sys.input a (v t))) :=
    funext fun t => sys.aux_augmentNonlin_f (x t) a (v t)
  -- the five fields of a run: measurable, integrable, continuous and the integral equation
  refine ⟨h0, hv, ?_, fun t ht => ?_, ?_, fun t ht => ?_, fun t ht => rfl⟩
  · rw [hf]
    exact (aux_pad n sys.m).continuous.comp_aestronglyMeasurable tr.meas
  · rw [hf]
    exact ⟨(aux_pad n sys.m).integrable_comp (tr.integrable t ht).1,
      (aux_pad n sys.m).integrable_comp (tr.integrable t ht).2⟩
  · refine continuousOn_pi.2 fun k => ?_
    refine Fin.addCases (fun e => ?_) (fun j => ?_) k
    · simpa [Fin.append_left] using continuousOn_pi.1 tr.cont e
    · simpa [Fin.append_right] using continuousOn_const
  · rw [hf]
    have hint := (aux_pad n sys.m).intervalIntegral_comp_comm (tr.integrable t ht)
    rw [hint]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa [aux_pad] using congrFun (tr.flow t ht) i
    · simp [aux_pad]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
