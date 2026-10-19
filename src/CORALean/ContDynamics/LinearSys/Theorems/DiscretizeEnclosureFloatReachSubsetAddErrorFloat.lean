module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.ReachErrorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInputFloatSubsetAddExcess
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemDiscretizeEnclosureFloatReachError
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetExact
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceSubsetAddBox
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A float sampled run lies in the exact held-input sampled set, plus its budget

The budget theorem of `reachInnerRepFloat`, and the float counterpart of
`reach_subset_discretize_reachSetExact_add_error`: the float run
`discretizeEnclosureFloat`'s `reach`, with `inputSolutionFloat` as its input
set, lies after `k` steps in the exact held-input sampled set — the sampled
system `discretize Δt` from `R₀`'s nominal zonotope, under the held-input
contribution `(∫₀^Δt e^{As} ds) U` of `U`'s nominal zonotope — widened by
`reachErrorFloat`.

By induction on `k`. A step peels, in the order the run applies them, the
reduction's box (`reduce_subset_add_box`), then the float step against the exact
held-input step (`timePointStepInputFloat_subset_add_excess`); the induction
hypothesis splits the previous float point into the exact set, the run's excess
and the input errors, and `e^{AΔt}` carries the last two into `[e^{AΔt}]` applied
to them, a member of which it is.

-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet Matrix NormedSpace
open scoped Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float sampled run is *contained in* the exact held-input sampled set from the nominal
zonotopes of `R₀` and `U`, widened by `reachErrorFloat`, at `Δt > 0` and an admissible order,
given both error boxes bracket `0`. -/
theorem LinearSys.discretizeEnclosureFloat_reach_subset_add_errorFloat (sys : LinearSys 𝕋 n)
    {Δt : 𝕋} (hΔt : 0 < toReal Δt) {η : ℕ} (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ}
    (ho : 0 < o) {R₀ U : Zonotope (Vec 𝕋 n)} (hR₀ : (0 : Vec ℝ n) ∈ R₀.I_error.construct)
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (k : ℕ) : -- --- CONCL ---
    ((sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).construct
      ⊆ (sys.discretize (toReal Δt)).reachSetExact (S := 𝒵)
          (nominal R₀)
          (Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt))
            (nominal U)) k
        + (sys.reachErrorFloat Δt η o ho R₀ U k).construct := by -- --- PROOF ---
  set eA := sys.expIntervalFloat Δt Δt η
  set Q := Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt))
    (nominal U)
  have he := sys.exp_mem_expIntervalFloat hη (t := toReal Δt) le_rfl le_rfl
  -- the claim with the two summands of the budget kept apart
  suffices h : ∀ k, ((sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).construct
      ⊆ (sys.discretize (toReal Δt)).reachSetExact (S := 𝒵)
          (nominal R₀) Q k
        + (sys.reachExcessFloat Δt η o ho R₀ U k).construct
        + (sys.reachInputErrorFloat Δt η U k).construct by
    intro x hx
    obtain ⟨_, ⟨z, hz, d, hd, rfl⟩, i, hi, rfl⟩ := h k hx
    have hdi : d + i ∈ (sys.reachErrorFloat Δt η o ho R₀ U k).construct := by
      show _ ∈ ContSet.construct
        (sys.reachExcessFloat Δt η o ho R₀ U k ⊞ sys.reachInputErrorFloat Δt η U k)
      exact Plus.plus_outer _ _ (Set.add_mem_add hd hi)
    exact ⟨z, hz, d + i, hdi, (add_assoc _ _ _).symm⟩
  intro k
  induction k with
  | zero =>
    -- `R₀`'s point is its nominal part plus its error box; nothing is owed to the input yet
    rintro _ ⟨a, ha, e₀, he₀, rfl⟩
    have h0 : (0 : Vec ℝ n) ∈ (sys.reachInputErrorFloat Δt η U 0).construct := by
      show (0 : Vec ℝ n) ∈ (Zonotope.point fun _ : Fin n => (zero : 𝕋)).construct
      rw [Zonotope.construct_point]
      funext i
      simp [toRealVec, toReal_zero]
    exact ⟨a + e₀, ⟨a, ha, e₀, Interval.zonotope_contains _ he₀, rfl⟩, 0, h0, add_zero _⟩
  | succ k ih =>
    set Rk := (sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
      ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩ with hRk
    set W := sys.timePointStepInputFloat Δt η Rk U
    have hRk0 : (0 : Vec ℝ n) ∈ Rk.I_error.construct :=
      sys.zero_mem_discretizeEnclosureFloat_reach_error hΔt.le hη ho hR₀ hU k
    intro x hx
    rw [sys.discretizeEnclosureFloat_reach_succ] at hx
    -- the reduction's box, then the float step against the exact held-input step
    obtain ⟨w, hw, g, hg, rfl⟩ := Zonotope.reduce_subset_add_box W o hx
    obtain ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, q, hq, rfl⟩, b, hb, rfl⟩, t, ht, rfl⟩ :=
      sys.timePointStepInputFloat_subset_add_excess hΔt hη hRk0 hU hw
    -- the previous float point: the exact set, the run's excess and the input errors
    obtain ⟨_, ⟨z, hz, d, hd, rfl⟩, i, hi, rfl⟩ := ih hy
    set E := exp (toReal Δt • Scalar.toRealMat sys.A)
    have hEd : E *ᵥ d ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eA
        (sys.reachExcessFloat Δt η o ho R₀ U k)).construct :=
      Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eA _
        (Set.mem_biUnion he ⟨d, hd, rfl⟩)
    have hEi : E *ᵥ i ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eA
        (sys.reachInputErrorFloat Δt η U k)).construct :=
      Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eA _
        (Set.mem_biUnion he ⟨i, hi, rfl⟩)
    -- the step's two outputs, each one more application of the same sum
    have hD : E *ᵥ d + b + g ∈ (sys.reachExcessFloat Δt η o ho R₀ U (k + 1)).construct := by
      show _ ∈ ContSet.construct
        ((Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eA
        (sys.reachExcessFloat Δt η o ho R₀ U k) ⊞ sys.timePointStepExcessFloat Δt η Rk U) ⊞
          Zonotope.reduceGirardBox W o)
      exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add hEd hb)) hg)
    have hI : E *ᵥ i + t ∈ (sys.reachInputErrorFloat Δt η U (k + 1)).construct := by
      show _ ∈ ContSet.construct
        (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eA
        (sys.reachInputErrorFloat Δt η U k) ⊞ sys.timePointStepErrorBoxFloat Δt η U)
      exact Plus.plus_outer _ _ (Set.add_mem_add hEi ht)
    -- the exact part is the exact set's own step
    have hZ : E *ᵥ z + q ∈ (sys.discretize (toReal Δt)).reachSetExact
        (S := 𝒵) (nominal R₀) Q (k + 1) :=
      ⟨_, ⟨z, hz, rfl⟩, q, hq, rfl⟩
    refine ⟨_, ⟨_, hZ, _, hD, rfl⟩, _, hI, ?_⟩
    simp only [Matrix.mulVec_add]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
