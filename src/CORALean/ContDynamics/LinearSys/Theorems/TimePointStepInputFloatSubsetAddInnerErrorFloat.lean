module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerErrorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInputFloatSubsetAddExcess
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet

@[expose] public section

/-!
# A float step lies in the exact held-input step, plus its budget

The budget theorem of `timePointStepInnerRepFloat`. The exact set is the
one-step reachable set of the sampled system `discretize r` from `X₀`'s nominal
zonotope, with the held-input contribution `(∫₀^r e^{As} ds) U` of `U`'s nominal
zonotope as its input: `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U`, a subset of the states
the system reaches at `t = r` (`discretize_reachSet_subset_inputReach`).

`timePointStepInputFloat_subset_add_excess` does the step; what is left is
`X₀`'s own error box, which `e^{Ar}` carries into `[e^{Ar}]` applied to it.
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

/-- The float step from `X₀` is *contained in* the exact held-input step from `X₀`'s nominal
zonotope, `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U`, widened by `timePointStepInnerErrorFloat`, at
`r > 0` and an admissible order. -/
theorem LinearSys.timePointStepInputFloat_subset_add_innerErrorFloat (sys : LinearSys 𝕋 n)
    {r : 𝕋} (hr : 0 < toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η)
    {X₀ U : Zonotope (Vec 𝕋 n)} (hX₀ : (0 : Vec ℝ n) ∈ X₀.E.construct)
    (hU : (0 : Vec ℝ n) ∈ U.E.construct) :
    (sys.timePointStepInputFloat r η X₀ U).construct
      ⊆ (sys.discretize (toReal r)).reachSet (S := 𝒵) (nominal X₀)
          (Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal r))
            (nominal U)) 1
        + (sys.timePointStepInnerErrorFloat r η X₀ U).construct := by -- --- PROOF ---
  set eA := sys.expIntervalFloat r r η
  have he := sys.exp_mem_expIntervalFloat hη (t := toReal r) le_rfl le_rfl
  intro x hx
  obtain ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩, b, hb, rfl⟩, t, ht, rfl⟩ :=
    sys.timePointStepInputFloat_subset_add_excess hr hη hX₀ hU hx
  -- `X₀`'s point splits into its nominal part and its error box, which `[e^{Ar}]` carries
  obtain ⟨a, ha, e₀, he₀, rfl⟩ := hy
  have he₀' : exp (toReal r • Scalar.toRealMat sys.A) *ᵥ e₀ ∈
    (Mtimes.mtimes (S := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) eA X₀.E.zonotope).construct :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eA _
      (Set.mem_biUnion he ⟨e₀, Interval.zonotope_contains _ he₀, rfl⟩)
  have hB : exp (toReal r • Scalar.toRealMat sys.A) *ᵥ e₀ + b + t
      ∈ (sys.timePointStepInnerErrorFloat r η X₀ U).construct := by
    show _ ∈ ContSet.construct
      ((Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eA
      X₀.E.zonotope ⊞ sys.timePointStepExcessFloat r η X₀ U) ⊞ sys.timePointStepErrorBoxFloat r η U)
    exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add he₀' hb)) ht)
  refine ⟨exp (toReal r • Scalar.toRealMat sys.A) *ᵥ a + w, ⟨_, ⟨a, ha, rfl⟩, w, hw, rfl⟩,
    _, hB, ?_⟩
  dsimp only
  rw [Matrix.mulVec_add]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
