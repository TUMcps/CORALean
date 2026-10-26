module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRun
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRunFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachInitFloatEncloses
public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachStepFloatEncloses

@[expose] public section

/-!
# The float state after `k` iterations stands for the exact one

By induction on `k`: the initial state stands for `maxBackReachInit`
(`maxBackReachInitFloat_encloses`) and one float iteration carries a state standing for an exact one
to a state standing for the exact iteration (`maxBackReachStepFloat_encloses`). The exact run takes
one Taylor order `η` for the initial state and every iteration, so the float run checks that the
searches at `t₀` and at `Δt` land on one order `ηr`, and is `none` otherwise. The float input
solution holds the exact one (`inputSolution_subset_inputSolutionFloat`), so the input `W₀` is only
asked to hold `W₀r` with error box `{0}`. The lines are those of [1, Alg. 3].

## Inputs
* `sys` – linear system
* `Bx` – conversion box
* `P₁` – first eroded float polytope
* `P₂` – second eroded float polytope
* `U` – input float zonotope
* `W₀` – initial disturbance float zonotope
* `Zw` – center trajectory contribution over a bracket
* `t₀` – float start time
* `Δt` – float step length
* `η` – Taylor order
* `ρ` – support oracle for bounded exact polytopes
* `P₁r` – first exact polytope
* `P₂r` – second exact polytope
* `Ur` – exact input zonotope
* `W₀r` – exact initial disturbance zonotope
* `Zwr` – exact center trajectory contribution
* `k` – iteration count

## Hypotheses
* `ht₀` – start time nonnegative
* `hΔt` – step length positive
* `hU0` – input error box contains zero
* `hU` – exact input zonotope inside the float one
* `hWE` – disturbance error box is zero
* `hW₀r` – exact disturbance zonotope inside the float one
* `hZw` – float center contribution holds the exact one
* `hP₁` – first float polytope inside the exact one
* `hP₂` – second float polytope inside the exact one
* `hP₁0` – first polytope error box contains zero
* `hP₂0` – second polytope error box contains zero
* `hker₁` – first float polytope has no equality rows
* `hker₂` – second float polytope has no equality rows
* `hkerr₁` – first exact polytope has no equality rows
* `hkerr₂` – second exact polytope has no equality rows
* `hP₁b` – the inequality rows of the first exact polytope bound it
* `hP₂b` – the inequality rows of the second exact polytope bound it

## Conclusion
* the float state after the iterations stands for the exact one
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachRunFloat_encloses (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) {U W₀ : Zonotope (Vec 𝕋 n)} {Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)}
    {t₀ Δt : 𝕋} {η : ℕ}
    (ρ : ∀ (P : CORALean.Real.HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁r P₂r : CORALean.Real.HPolytope (Vec ℝ n))
    (Ur W₀r : CORALean.Real.Zonotope (Vec ℝ n)) (Zwr : ℝ → CORALean.Real.Zonotope (Vec ℝ n))
    (ht₀ : 0 ≤ toReal t₀) (hΔt : 0 < toReal Δt) (hU0 : (0 : Vec ℝ n) ∈ U.I_error.construct)
    (hU : U.construct ⊆ construct Ur) (hWE : W₀.I_error = Interval.point fun _ => FloatOps.zero)
    (hW₀r : W₀r.construct ⊆ W₀.construct)
    (hZw : ∀ (tLo tHi : 𝕋) (t : ℝ), toReal tLo ≤ t → t ≤ toReal tHi →
      construct (Zwr t) ⊆ (Zw tLo tHi).construct) (hP₁ : P₁.construct ⊆ P₁r.construct)
    (hP₂ : P₂.construct ⊆ P₂r.construct) (hP₁0 : (0 : Vec ℝ n) ∈ P₁.I_error.construct)
    (hP₂0 : (0 : Vec ℝ n) ∈ P₂.I_error.construct)
    (hker₁ : ∀ i (y : Vec ℝ n), (toRealMat P₁.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i (y : Vec ℝ n), (toRealMat P₂.Ae *ᵥ y) i = 0)
    (hkerr₁ : ∀ (i : Fin P₁r.me) (y : Vec ℝ n), P₁r.Ae i y = 0)
    (hkerr₂ : ∀ (i : Fin P₂r.me) (y : Vec ℝ n), P₂r.Ae i y = 0)
    (hP₁b : Bornology.IsBounded P₁r.dropEqs.construct)
    (hP₂b : Bornology.IsBounded P₂r.dropEqs.construct) (k : ℕ) : -- --- CONCL ---
    ∀ s ∈ sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k,
      ∃ ηr, sys.reachOrderFloat t₀ t₀ η = some ηr ∧ sys.reachOrderFloat Δt Δt η = some ηr ∧
        s.Encloses
          (sys.maxBackReachRun ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr (toReal t₀) (toReal Δt) ηr
            k) := by -- --- PROOF ---
  intro s (h : sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k = some s)
  induction k generalizing s with
  | zero =>
    -- the run's own check makes the two searches agree
    unfold LinearSys.maxBackReachRunFloat at h
    split_ifs at h with hc
    obtain ⟨ηr, hη₀⟩ : ∃ ηr, sys.reachOrderFloat t₀ t₀ η = some ηr := by
      unfold LinearSys.maxBackReachInitFloat at h
      cases hs : sys.reachOrderFloat t₀ t₀ η with
      | none => simp [hs] at h
      | some e => exact ⟨e, rfl⟩
    exact ⟨ηr, hη₀, hc ▸ hη₀,
      sys.maxBackReachInitFloat_encloses Ur W₀r ht₀ hU0 hU hWE hW₀r _ hη₀ _ h⟩
  | succ k ih =>
    -- one float iteration from the state of the run before it
    obtain ⟨sk, hsk, hstep⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ηr, hη₀, hη, hsr⟩ := ih _ hsk
    exact ⟨ηr, hη₀, hη, sys.maxBackReachStepFloat_encloses Bx P₁ P₂ ρ P₁r P₂r Ur W₀r
      Zwr _ hsr hΔt hU0 hU hWE hW₀r (hZw _ _ _ hsr.tEnc_inf_le hsr.le_tEnc_sup) hP₁ hP₂ hP₁0 hP₂0
        hker₁
      hker₂ hkerr₁ hkerr₂ hP₁b hP₂b _ hη _ hstep⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
