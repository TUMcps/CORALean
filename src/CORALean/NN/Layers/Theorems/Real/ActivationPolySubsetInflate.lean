import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.NN.Layers.Theorems.CoeffListCoord
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# The exact polynomial activation layer, read the other way

ℝ-only, `evalPoly` and `plus` being exact only there. `enclose_outer` says the enclosed set
contains the image; this says how much larger it is. Every member is the polynomial at some point
of the input plus something from the residual box, so it is within `2 · error` of that point's
true value — the fit's own error and the box's, each once. The input box is ordered, a polynomial
zonotope never being empty, and the error therefore nonnegative, soundness bounding an absolute
value at a point the box contains.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet

variable {σ : ℝ → ℝ} {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the polynomial part, one neuron's own fit per coordinate, read without the scalar
theorem aux_coord (P : LayerRelaxation ℝ n m) (J : Float.Interval (Vec ℝ n)) (i : Fin n) :
    ((P.coeffList J).map fun v => v i) = List.ofFn fun k => (P i).coeffs (J.inf i) (J.sup i) k :=
  LayerRelaxation.coeffList_coord P J i


-- =======================================  MAIN THEOREM  ======================================= --

/-- The enclosed set is inside the image inflated by `ε`, at any `ε` the neurons' doubled errors
fit under. -/
theorem Layer.activationPoly_subset_inflate {P : LayerRelaxation ℝ n m}
    (hPs : ∀ i, (P i).Sound σ) (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ∀ i, 2 * (P i).error (s.interval.inf i) (s.interval.sup i) ≤ ε) :
    construct ((Layer.activationPoly P).enclose s)
      ⊆ (fun x i => σ (x i)) '' construct s + Metric.closedBall 0 ε := by -- --- PROOF ---
  set J : Float.Interval (Vec ℝ n) := ⟨s.interval.inf, s.interval.sup⟩
  -- the box is ordered, so `sound` at its left end says the error is nonnegative
  have herr : ∀ i, 0 ≤ (P i).error (s.interval.inf i) (s.interval.sup i) := fun i =>
    le_trans (abs_nonneg _)
      ((hPs i).sound (le_refl (s.interval.inf i)) (s.interval_inf_le_sup i))
  intro y hy
  have hy2 : y ∈ (s.dependent.evalPoly (P.coeffList J)).construct
      + (Interval.polyZonotope (P.box J).nominal).construct := by
    rw [PolyZonotope.plus_exact]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy2
  -- the polynomial part has no independent block, so it is a point of the factors
  obtain ⟨a, ha, hua⟩ := (s.dependent.evalPoly (P.coeffList J)).exists_point_of_q_zero
    (PolyZonotope.evalPoly_q s.dependent (P.coeffList J)) hu
  obtain ⟨a', ha'bound, ha'⟩ : ∃ a' : Fin s.dependent.p → ℝ, (∀ j, |a' j| ≤ 1) ∧
      (fun k => a' (Fin.cast (s.dependent.evalPoly_p (P.coeffList J)) k)) = a :=
    ⟨fun j => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList J)).symm j),
      fun j => ha _, by funext k; simp⟩
  have hxs : s.dependent.point a' ∈ s.construct := by
    rw [PolyZonotope.dependent_exact s]
    exact s.dependent.point_mem_construct ha'bound
  have hxbox := PolyZonotope.interval_contains s hxs
  -- the polynomial the set evaluates to, one neuron's own fit per coordinate
  have hpval : (s.dependent.evalPoly (P.coeffList J)).point
        (fun k => a' (Fin.cast (s.dependent.evalPoly_p (P.coeffList J)) k))
      = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i))
          (s.dependent.point a' i) := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [aux_coord, PolyZonotope.evalPolyReal_ofFn]
    rfl
  have hueq : u = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i))
      (s.dependent.point a' i) := by
    rw [hua, ← hpval, ha']
  -- the residual box, centred at zero, reaches no further than half the budget
  have hbox : ∀ i, |(P.box J).nominal.inf i| ≤ ε / 2 ∧ |(P.box J).nominal.sup i| ≤ ε / 2 := by
    intro i
    constructor
    · show |-(P i).error (s.interval.inf i) (s.interval.sup i)| ≤ ε / 2
      rw [abs_neg, abs_of_nonneg (herr i)]
      linarith [hP i]
    · show |(P i).error (s.interval.inf i) (s.interval.sup i)| ≤ ε / 2
      rw [abs_of_nonneg (herr i)]
      linarith [hP i]
  have hvnorm : ‖v‖ ≤ ε / 2 :=
    Interval.polyZonotope_norm_le (by linarith) (fun i => (hbox i).1) (fun i => (hbox i).2) hv
  -- and each coordinate is within the fit's error plus the box's, which is `2 · error`
  have hres : ∀ i, |(u + v) i - σ (s.dependent.point a' i)| ≤ ε := by
    intro i
    have hvi : |v i| ≤ ε / 2 := by
      have h := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at h
      linarith
    have hsound : |σ (s.dependent.point a' i)
        - evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (s.dependent.point a' i)|
        ≤ (P i).error (s.interval.inf i) (s.interval.sup i) :=
      (hPs i).sound (hxbox i).1 (hxbox i).2
    obtain ⟨hd1, hd2⟩ := abs_le.mp hsound
    obtain ⟨hv1, hv2⟩ := abs_le.mp hvi
    show |u i + v i - σ (s.dependent.point a' i)| ≤ ε
    rw [congrFun hueq i, abs_le]
    constructor <;> linarith [hP i]
  -- that bound, read as a vector, is exactly what the ball holds
  have hball : (u + v) - (fun i => σ (s.dependent.point a' i))
      ∈ Metric.closedBall (0 : Vec ℝ n) ε := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hε]
    intro i
    rw [Real.norm_eq_abs]
    exact hres i
  have hmem := Set.add_mem_add
    (show (fun i => σ (s.dependent.point a' i))
      ∈ (fun x i => σ (x i)) '' construct s from ⟨s.dependent.point a', hxs, rfl⟩) hball
  have heq : (fun i => σ (s.dependent.point a' i))
      + ((u + v) - fun i => σ (s.dependent.point a' i)) = u + v := by abel
  rwa [heq] at hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
