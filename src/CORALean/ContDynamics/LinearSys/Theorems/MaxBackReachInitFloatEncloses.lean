module

public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloatEncloses
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInit
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInitFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemAdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.ConZonotope.Float.Theorems.OriginExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatSubsetAddBox
public import CORALean.ContSet.Zonotope.Float.Theorems.OriginExact
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesIntervalMatError
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# The float state before the first iteration stands for the exact one

`maxBackReachInitFloat` against `maxBackReachInit`, at the order the float search raised to: the
float `Z̲_U(t₀)` is `[∫₀^{t₀}] U`, whose points are the exact integral applied to a point of `U`
plus an error within `mtimesIntervalMatBox` (`mtimesIntervalMat_subset_add_box`, at the exact
integral, a member of the interval matrix); the float `U` is asked to lie inside the exact one,
and `Ẑ_{W₀}(t₀)` to hold the exact one, which the caller proves of the float input solution; the
rest is the origin on both sides.
The lines are those of [1, Alg. 3].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachInitFloat_encloses (sys : LinearSys 𝕋 n) {U W₀ : Zonotope (Vec 𝕋 n)}
    {t₀ : 𝕋} {η η' : ℕ} {s : LinearSys.MaxBackReachStateFloat 𝕋 n}
    (h : sys.maxBackReachInitFloat U W₀ t₀ η = some s) (hη' : sys.reachOrderFloat t₀ t₀ η = some η')
    (Ur W₀r : CORALean.Real.Zonotope (Vec ℝ n)) (ht₀ : 0 ≤ toReal t₀)
    (hU0 : (0 : Vec ℝ n) ∈ U.I_error.construct) (hU : U.construct ⊆ construct Ur)
    (hWE : W₀.I_error = Interval.point fun _ => FloatOps.zero)
        (hW₀r : W₀r.construct ⊆ W₀.construct) : -- --- STMT ---
    s.Encloses (sys.maxBackReachInit Ur W₀r (toReal t₀) η') := by -- --- PROOF ---
  -- the float state, with the order the search found
  simp only [LinearSys.maxBackReachInitFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η'', hη'', rfl⟩ := h
  obtain rfl : η' = η'' := Option.some.inj (hη'.symm.trans hη'')
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  have hW := sys.inputSolution_subset_inputSolutionFloat ht₀ hadm hWE hW₀r
  -- the exact integral is in the float interval matrix
  have hI := sys.expIntegral_mem_adaptiveIntegralFloat ht₀ hadm
  set I := MatExp.adaptiveIntegral (Interval.point sys.A) t₀ η'
  refine ⟨le_rfl, le_rfl, ?_, ?_, hW, ?_, ?_⟩
  -- the error box of `Z̲_U` holds `0`
  · show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat I U).materialise).I_error.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_mtimesIntervalMat_error hI hU0
  -- a point of the float `Z̲_U` is the exact integral of a point of `U`, plus the box
  · intro x hx
    have hx' : x ∈ (Zonotope.mtimesIntervalMat I U).construct := by
      have h := hx
      simp only [Mtimes.mtimes, Zonotope.materialise_eq] at h
      exact h
    obtain ⟨_, ⟨u, hu, rfl⟩, b, hb, rfl⟩ :=
      Zonotope.mtimesIntervalMat_subset_add_box I U hU0 hI hx'
    refine ⟨_, ?_, b, fun i => Interval.abs_le_magnitude hb i, rfl⟩
    show _ ∈ (CORALean.Real.Zonotope.mtimes _ Ur).construct
    rw [← CORALean.Real.Zonotope.mtimes_exact]
    exact ⟨u, hU hu, rfl⟩
  -- the exact disturbance set is the point `0`, and so is the float one
  · intro x hx
    have hx0 : x = 0 := (CORALean.Real.Zonotope.mem_ofPoint_iff _ _).mp hx
    rw [hx0, Zonotope.origin_exact]
    rfl
  -- both summands of `R̂^{∃∀}` are the point `0`, as is the exact one
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha0 : a = 0 := by
      have := ha
      rw [ConZonotope.origin_exact] at this
      exact this
    have hb0 : b = 0 := by
      have h := Set.mem_neg.mp hb
      rw [Zonotope.origin_exact] at h
      simpa using h
    show a + b ∈ construct (CORALean.Real.Zonotope.ofPoint (0 : Vec ℝ n)).conZonotope
    rw [ha0, hb0, add_zero]
    exact (CORALean.Real.Zonotope.conZonotope_exact _).subset
      (CORALean.Real.Zonotope.mem_ofPoint _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
