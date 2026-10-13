import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialStateFloat
import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonTestFloatSound

/-!
# What `consistentInitialStateFloat` returns

A returned `y'` lies within `tol`, in the sup norm, of exactly one zero of `g(x₀, ·, u₀)`: a
consistent initial algebraic state exists there and is unique in that ball. The real
`consistentInitialState_spec` claims only CORA's stopping test, a last Newton step below `tol`;
here the test the float run adds (`newtonTestFloat_sound`) makes the claim about the root itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A returned point is within `tol` of exactly one solution of `g(x₀, y, u₀) = 0`. -/
theorem NonlinDASys.FloatModel.Encloses.consistentInitialStateFloat_root
    {fm : NonlinDASys.FloatModel 𝕋 n p m} {sys : NonlinDASys n p m} (hfm : fm.Encloses sys)
    (tol : 𝕋) (fuel : ℕ) (x₀ : Vec 𝕋 n) (u₀ : Vec 𝕋 m) (y₀ y' : Vec 𝕋 p)
    (h : fm.consistentInitialStateFloat tol fuel x₀ u₀ y₀ = some y') :
    ∃! y, y ∈ Metric.closedBall (toRealVec y') (toReal tol) ∧
      sys.g (toRealVec x₀) y (toRealVec u₀) = 0 := by -- --- PROOF ---
  unfold NonlinDASys.FloatModel.consistentInitialStateFloat at h
  obtain ⟨yv, -, hy⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at hy
  split_ifs at hy with htest
  rw [Option.some.inj hy] at htest
  have hx₀ : toRealVec x₀ ∈ (Interval.point x₀).construct := Interval.mem_point x₀
  have hu₀ : toRealVec u₀ ∈ (Interval.point u₀).construct := Interval.mem_point u₀
  refine NonlinDASys.newtonTestFloat_sound (fun y => sys.g (toRealVec x₀) y (toRealVec u₀)) _ _
    (fun Y a ha => hfm.g_mem _ Y _ _ hx₀ a ha _ hu₀) (fun Y a ha a' ha' => ?_) y' tol htest
  -- at a fixed `x₀` the slope of `g` is its `F` block
  obtain ⟨D, -, F, hF, hslope⟩ := hfm.slope_g _ Y _ _ hx₀ _ hx₀ a ha a' ha' _ hu₀
  refine ⟨F, hF, ?_⟩
  rw [hslope, sub_self, Matrix.mulVec_zero, zero_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
