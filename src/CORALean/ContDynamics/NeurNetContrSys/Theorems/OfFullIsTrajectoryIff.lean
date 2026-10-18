module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic

@[expose] public section

/-!
# With no external input, the loop is the one in which the network drives every input

`ofFull plant contr` has `m = nrOfInputs plant`, so `nExt = 0` and the plant's input is the
network's output alone (`input a e = a`). Its `IsTrajectory`, for any nonempty `U_ext` (a set of
`Vec ℝ 0`s, which all coincide), is a start in `R₀` and, on each period, a run of the plant under
the held input `π(x(i dt))` — the statement of the closed loop before external inputs were
modelled, but for the input set the plant is handed, `{π(x(i dt))}` where it was `univ`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With `m = M`, `[a; e]` is `a`. -/
theorem aux_joinInput_full {M : ℕ} (a : Vec ℝ M) (e : Vec ℝ (M - M)) :
    joinInput (le_refl M) a e = a := by
  funext i
  simp [joinInput, i.isLt]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.ofFull_isTrajectory_iff (plant : P)
    (contr : NeuralNetwork S n (nrOfInputs plant)) (dt : ℝ)
    {π : Vec ℝ n → Vec ℝ (nrOfInputs plant)} {H : ℕ} {R₀ : S n}
    {U_ext : Set (Vec ℝ (NeurNetContrSys.ofFull plant contr dt).nExt)} (hU : U_ext.Nonempty)
    {W : Set (Vec ℝ (nrOfDisturbances plant))} {x : ℝ → Vec ℝ n}
    {v : ℝ → Vec ℝ (NeurNetContrSys.ofFull plant contr dt).nExt}
    {w : ℝ → Vec ℝ (nrOfDisturbances plant)} : -- --- STMT ---
    (NeurNetContrSys.ofFull plant contr dt).IsTrajectory π H R₀ U_ext W x v w ↔
      x 0 ∈ construct R₀ ∧ ∀ i < H,
        ContDynamics.IsTrajectory plant (Set.Icc 0 dt) Set.univ {π (x ((i : ℝ) * dt))} W
          (fun t => x ((i : ℝ) * dt + t)) (fun _ => π (x ((i : ℝ) * dt)))
          (fun t => w ((i : ℝ) * dt + t)) := by -- --- PROOF ---
  -- the plant's input is the network's output, and its input set the singleton
  have hin : ∀ a e, (NeurNetContrSys.ofFull plant contr dt).input a e = a := fun a e =>
    aux_joinInput_full a e
  have hset : ∀ a : Vec ℝ (NeurNetContrSys.ofFull plant contr dt).m,
      (NeurNetContrSys.ofFull plant contr dt).inputSet {a} U_ext = {a} := by
    intro a
    ext u
    obtain ⟨e₀, he₀⟩ := hU
    constructor
    · rintro ⟨a', ha', e, _, rfl⟩
      rw [Set.mem_singleton_iff.1 ha', hin]
      rfl
    · intro hu
      exact ⟨a, rfl, e₀, he₀, by rw [Set.mem_singleton_iff.1 hu, hin]⟩
  -- both directions rewrite the input and the input set, then agree
  constructor
  · intro h
    refine ⟨h.init, fun i hi => ?_⟩
    have := h.flow i hi
    simp only [hin, hset] at this
    exact this
  · rintro ⟨h0, hf⟩
    refine ⟨h0, fun i hi => ?_⟩
    have := hf i hi
    simp only [hin, hset]
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
