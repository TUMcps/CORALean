module

public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
public import CORALean.NN.Layers.Definitions.PolyFamily
public import CORALean.NN.Operations.IsConvergent
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.NN.Layers.Theorems.CoeffListCoord
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalPolyZonotopeNormLe
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilySound
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeIntervalInfLeSup
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound

@[expose] public section

/-!
# The sigmoid activation layer converges under refinement

ℝ-only, as convergence is: the nonlinear half of [1, Prop. 4.13], at a layer someone would
actually build.

## Inputs
* `n` – layer width

## Hypotheses
* none

## Conclusion
* the sigmoid layer converges under refinement

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- Each level of the family is accurate on its range. -/
private theorem aux_polyRelaxationFamily_error_lt {σ σ' : ℝ → ℝ} {Mσ : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) (o : ℕ) {l u : ℝ}
    (hl : -(o : ℝ) ≤ l) (hlu : l ≤ u) (hu : u ≤ (o : ℝ)) :
    ((polyRelaxationFamily hd hσ).rel o).error l u < 1 / ((o : ℝ) + 1) :=
  (exists_polyRelaxation_error_lt (L := -(o : ℝ)) (U := (o : ℝ)) hd hσ
    (show (0 : ℝ) < 1 / ((o : ℝ) + 1) by positivity)).choose_spec.choose_spec.2 l u hl hlu hu

end


section
variable {n : ℕ}
open Pointwise ContSet
variable {σ : ℝ → ℝ} {m n : ℕ}

-- the polynomial part, one neuron's own fit per coordinate, read without the scalar
private theorem aux_coeffListCoord (P : LayerRelaxation ℝ n m) (J : Float.Interval (Vec ℝ n))
    (i : Fin n) :
    ((P.coeffList J).map fun v => v i) = List.ofFn fun k => (P i).coeffs (J.inf i) (J.sup i) k :=
  LayerRelaxation.coeffList_coord P J i


/-- The enclosed set is inside the image inflated by `ε`, at any `ε` the neurons' doubled errors
fit under. -/
private theorem Layer.aux_activationPoly_subset_inflate {P : LayerRelaxation ℝ n m}
    (hPs : ∀ i, (P i).IsSound σ) (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ∀ i, 2 * (P i).error (s.interval.inf i) (s.interval.sup i) ≤ ε) : -- --- CONCL ---
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
    rw [aux_coeffListCoord, PolyZonotope.evalPolyReal_ofFn]
    rfl
  have hueq : u = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i))
      (s.dependent.point a' i) := by
    rw [hua, ← hpval, ha']
  -- the residual box, centered at zero, reaches no further than half the budget
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

end


section
variable {n : ℕ}

/-- The level one neuron needs: past both ends of its own box, and past `2 / ε`. -/
private theorem aux_exists_level_one (l u : ℝ) {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ∃ o : ℕ, (-(o : ℝ) ≤ l ∧ u ≤ (o : ℝ)) ∧ 2 * (1 / ((o : ℝ) + 1)) ≤ ε := by -- --- PROOF ---
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  -- one level past `M` and past both ceilings serves this neuron
  obtain ⟨o, hMo, hlo, huo⟩ : ∃ o : ℕ, M ≤ o ∧ ⌈|l|⌉₊ ≤ o ∧ ⌈|u|⌉₊ ≤ o :=
    ⟨max M (max ⌈|l|⌉₊ ⌈|u|⌉₊), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hl : |l| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hlo)
  have hu : |u| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr huo)
  have hMr : (M : ℝ) ≤ (o : ℝ) := Nat.cast_le.mpr hMo
  have hopos : (0 : ℝ) < (o : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) o]
  refine ⟨o, ⟨by linarith [neg_abs_le l], by linarith [le_abs_self u]⟩, ?_⟩
  -- the level is past `M`, which was chosen past `2 / ε`
  have h2 : 2 / ε < (o : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at h2
  rw [mul_one_div, div_le_iff₀ hopos]
  linarith


/-- A level per neuron, each covering that neuron's own box and leaving `2 · error` under `ε`. -/
private theorem aux_exists_level (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : OrderPattern n, ∀ i,
      (-((t i : ℕ) : ℝ) ≤ s.interval.inf i ∧ s.interval.sup i ≤ ((t i : ℕ) : ℝ))
        ∧ 2 * (1 / (((t i : ℕ) : ℝ) + 1)) ≤ ε :=
  ⟨fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose,
    fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose_spec⟩


/-- Raising the pattern puts the enclosed set inside any inflation of the exact image. -/
private theorem Layer.aux_activationPolyRefinable_convergent {σ σ' : ℝ → ℝ} {Mσ : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) : -- --- CONCL ---
    (Layer.activationPolyRefinable (n := n) (polyRelaxationFamily hd hσ)
      (polyRelaxationFamily_sound hd hσ)).IsConvergent := by -- --- PROOF ---
  intro s ε hε
  obtain ⟨t, ht⟩ := aux_exists_level s hε
  refine ⟨t, Layer.aux_activationPoly_subset_inflate
    ((polyRelaxationFamily hd hσ).atPattern_sound (polyRelaxationFamily_sound hd hσ) t)
    s hε.le fun i => ?_⟩
  -- padding leaves the error alone, so the neuron's own level is what counts
  have hpad : ((polyRelaxationFamily hd hσ).atPattern t i).error
      = ((polyRelaxationFamily hd hσ).rel (t i)).error := rfl
  rw [hpad]
  have herr := aux_polyRelaxationFamily_error_lt hd hσ (t i) (ht i).1.1
    (s.interval_inf_le_sup i) (ht i).1.2
  linarith [(ht i).2]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPolySigmoid_convergent (n : ℕ) :
    (Layer.activationPolyRefinable (n := n) sigmoidPolyFamily sigmoidPolyFamily_sound).IsConvergent
        :=
  Layer.aux_activationPolyRefinable_convergent hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
