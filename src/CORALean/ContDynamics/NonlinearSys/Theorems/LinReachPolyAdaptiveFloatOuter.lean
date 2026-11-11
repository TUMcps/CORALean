module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyAdaptivePassFloatOuter

@[expose] public section

/-!
# One step of CORA's poly-adaptive algorithm holds every run of the real system

Whatever the tuning decides, the sets `linReachPolyAdaptiveFloat` returns are those of one pass,
`linReachPolyAdaptivePassFloat`, from the step's start set at that pass's own step size: the current
pass, or the one saved as the horizon's when the tuned step is the horizon. That is the invariant of
the outer loop (its start set never changes, and every saved pass is a pass from it), proved by
induction on the loop's fuel; `linReachPolyAdaptivePassFloat_outer` does the rest. The time advances
by that step size, exactly.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `o` – adaptive options
* `st` – state before the step

## Hypotheses
* `h` – model encloses system
* `hfix` – the abstraction error's fixed point confines the runs
* `htrack` – the static error follows the factors of the start set, at every step size

## Conclusion
* a successful step advances the time and encloses every run over the step and at its end
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A pass from `R` at step size `Δt`, at some tensor order and initial error. -/
private def aux_isPass (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) (R : PolyZonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) : Prop :=
  ∃ e, fm.linReachPolyAdaptivePassFloat U ⟨⟨Δt, o.taylorTerms⟩, o.zonotopeOrder⟩ o.enlarge
    o.redFactor o.prec o.fuel R e = some P

omit [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The orders' update leaves the start set alone. -/
private theorem aux_adaptiveOrders_R (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) : -- --- CONCL ---
    (fm.step_adaptiveOrdersPoly U o L P).R = L.st.R := by -- --- PROOF ---
  unfold NonlinearSys.FloatHessModel.step_adaptiveOrdersPoly
  simp only [apply_ite NonlinearSys.LinReachPolyAdaptiveState.R, ite_self]

/-- The run at the horizon keeps the start set, and keeps the saved pass or saves `P` at the
current step size. -/
private theorem aux_adaptiveHorizon (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) : -- --- CONCL ---
    (fm.step_adaptiveHorizonPoly U o L P).st.R = L.st.R ∧
      ((fm.step_adaptiveHorizonPoly U o L P).hor = L.hor ∨
        (fm.step_adaptiveHorizonPoly U o L P).hor = some (L.timeStep, P)) := by -- --- PROOF ---
  have hR := aux_adaptiveOrders_R fm U o L P
  unfold NonlinearSys.FloatHessModel.step_adaptiveHorizonPoly
  dsimp only
  split_ifs <;> first | exact ⟨hR, Or.inr rfl⟩ | exact ⟨hR, Or.inl rfl⟩

/-- A decision keeps the start set; a continuation keeps the saved pass or saves `P` at the
current step size, and an end keeps both and the step size. -/
private theorem aux_decide (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) : -- --- CONCL ---
    (∀ L₁, fm.step_linReachPolyAdaptiveDecide U o L P = .inl L₁ →
      L₁.st.R = L.st.R ∧ (L₁.hor = L.hor ∨ L₁.hor = some (L.timeStep, P))) ∧
    (∀ L₂, fm.step_linReachPolyAdaptiveDecide U o L P = .inr L₂ →
      L₂.st.R = L.st.R ∧ L₂.hor = L.hor ∧ L₂.timeStep = L.timeStep) := by -- --- PROOF ---
  obtain ⟨hR, hhor⟩ := aux_adaptiveHorizon fm U o L P
  unfold NonlinearSys.FloatHessModel.step_linReachPolyAdaptiveDecide
  dsimp only
  constructor
  · intro L₁ h
    split_ifs at h <;> cases h <;> exact ⟨hR, hhor⟩
  · intro L₂ h
    split_ifs at h
    cases h
    refine ⟨?_, rfl, rfl⟩
    unfold NonlinearSys.FloatHessModel.step_adaptiveFinishPoly
    dsimp only
    exact aux_adaptiveOrders_R fm U o L P

/-- The outer loop keeps its start set, saves only passes from it, and ends on one. -/
private theorem aux_loop (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) (R : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ (fuel : ℕ) (L L' : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
      (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n),
      fm.step_linReachPolyAdaptiveLoop U o fuel L = some (L', P) → L.st.R = R →
      (∀ q, L.hor = some q → aux_isPass fm U o R q.1 q.2) →
      L'.st.R = R ∧ (∀ q, L'.hor = some q → aux_isPass fm U o R q.1 q.2) ∧
        aux_isPass fm U o R L'.timeStep P := by -- --- PROOF ---
  -- induction on the fuel, for every loop state
  intro fuel
  induction fuel with
  | zero => intro L L' P h; simp [NonlinearSys.FloatHessModel.step_linReachPolyAdaptiveLoop] at h
  | succ fuel ih =>
    intro L L' P h hR hhor
    unfold NonlinearSys.FloatHessModel.step_linReachPolyAdaptiveLoop at h
    split at h
    · exact ih _ _ _ h hR hhor
    · -- a pass: the decision continues or ends the loop
      rename_i P₀ hpass
      have hgood : aux_isPass fm U o R L.timeStep P₀ := ⟨_, hR ▸ hpass⟩
      split at h
      · rename_i L₁ hdec
        obtain ⟨hR₁, hhor₁⟩ := (aux_decide fm U o L P₀).1 L₁ hdec
        refine ih _ _ _ h (hR₁.trans hR) fun q hq => ?_
        rcases hhor₁ with h₁ | h₁
        · exact hhor q (h₁ ▸ hq)
        · rw [h₁] at hq; cases hq; exact hgood
      · rename_i L₂ hdec
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hR₂, hhor₂, hΔt₂⟩ := (aux_decide fm U o L P₀).2 L₂ hdec
        exact ⟨hR₂.trans hR, fun q hq => hhor q (hhor₂ ▸ hq), hΔt₂ ▸ hgood⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step advances the time, and every run of `sys` from the step's start set under
inputs in `U` is in `Rτ` over the step and in `R` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachPolyAdaptiveFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (hfix : sys.HasFixedPointConfinement) {U : Zonotope (Vec 𝕋 m)}
    {o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋}
    (htrack : ∀ (R : PolyZonotope (Vec 𝕋 n)) (Δt : 𝕋),
      fm.HasTrackedPassStaticError U ⟨⟨Δt, o.taylorTerms⟩, o.zonotopeOrder⟩ o.redFactor o.prec R)
    {st : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n} : -- --- CONCL ---
    ∀ s' ∈ fm.linReachPolyAdaptiveFloat U o st,
      st.t < s'.t ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 ((s'.t - st.t : ℚ) : ℝ)) st.R.toSet U.toSet x u
          y →
        (∀ t ∈ Set.Icc 0 ((s'.t - st.t : ℚ) : ℝ), x t ∈ s'.Rτ.toSet) ∧
          x ((s'.t - st.t : ℚ) : ℝ) ∈ s'.R.toSet := by -- --- PROOF ---
  intro s' (hs : fm.linReachPolyAdaptiveFloat U o st = some s')
  unfold NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat at hs
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
  obtain ⟨⟨L, P⟩, hL, hpure⟩ := hs
  simp only [pure, Option.some.injEq] at hpure
  subst hpure
  obtain ⟨_, hhor, hP⟩ := aux_loop fm U o st.R _ _ _ _ hL
    (by dsimp only; split_ifs <;> rfl) (by intro q hq; simp at hq)
  -- the sets returned are a pass's, at its own step size
  set F := if L.timeStepequalHorizon then L.hor.getD (L.timeStep, P) else (L.timeStep, P)
  have hF : aux_isPass fm U o st.R F.1 F.2 := by
    simp only [F]
    split_ifs
    · cases hq : L.hor with
      | none => simpa using hP
      | some q => simpa using hhor q hq
    · exact hP
  -- the pass's guarantee, and its step size as the time advanced
  obtain ⟨e, hpass⟩ := hF
  obtain ⟨hpos, hout⟩ := h.linReachPolyAdaptivePassFloat_outer hfix (htrack _ _) _ hpass
  have hΔ : ((st.t + ToRat.toRat F.1 - st.t : ℚ) : ℝ) = toReal F.1 := by
    rw [add_sub_cancel_left, ToRat.toReal_toRat]
  refine ⟨?_, fun {x u y} traj => ?_⟩
  · have : (0 : ℝ) < ((ToRat.toRat F.1 : ℚ) : ℝ) := by rw [ToRat.toReal_toRat]; exact hpos
    exact lt_add_of_pos_right _ (by exact_mod_cast this)
  · dsimp only
    rw [hΔ] at traj ⊢
    exact hout traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
