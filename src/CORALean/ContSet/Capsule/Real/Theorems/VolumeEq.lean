module

public import CORALean.ContSet.Capsule.Real.Operations.Volume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# The volume of a capsule

`Capsule.volume` is the Lebesgue measure of the capsule (for `n > 0`), exactly. A rotation takes
the segment `[-g, g]` onto the first axis, and the measure is the same. The capsule is then, in the
first coordinate `s` and the remaining ones `w`, the set where `max(|s| - ‖g‖, 0)² + ‖w‖² ≤ r²`: the
slice at `w` is an interval of length `2‖g‖ + 2 sqrt(r² - ‖w‖²)` when `‖w‖ ≤ r`, so by Fubini
the measure is `2‖g‖` times the measure of the `(n-1)`-ball, plus the integral of the ball's own
slice lengths, which is the measure of the `n`-ball (the same computation at `g = 0`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory Set

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The capsule on the first axis, in the coordinates `(s, w)`. -/
def aux_P (m : ℕ) (L r : ℝ) : Set (ℝ × (Fin m → ℝ)) :=
  {p | (max (|p.1| - L) 0) ^ 2 + ∑ i, (p.2 i) ^ 2 ≤ r ^ 2}

-- the coordinate description is a measurable set, so Fubini applies
theorem aux_P_meas (L r : ℝ) : MeasurableSet (aux_P m L r) := by
  unfold aux_P
  exact measurableSet_le (by fun_prop) measurable_const

-- the slice of the capsule at a fixed `w`, as a condition on `s` alone
theorem aux_slice_eq (L r : ℝ) (w : Fin m → ℝ) :
    (fun s : ℝ => (s, w)) ⁻¹' aux_P m L r
      = {s : ℝ | (max (|s| - L) 0) ^ 2 ≤ r ^ 2 - ∑ i, (w i) ^ 2} := by
  ext s
  simp only [aux_P, mem_preimage, mem_setOf_eq]
  constructor <;> intro h <;> linarith

-- that slice is an interval, centered, of half-length `L + sqrt ρ`
theorem aux_slice_icc {L ρ : ℝ} (hρ : 0 ≤ ρ) :
    {s : ℝ | (max (|s| - L) 0) ^ 2 ≤ ρ} = Icc (-(L + √ρ)) (L + √ρ) := by -- --- PROOF ---
  ext s
  simp only [mem_setOf_eq, mem_Icc]
  have h0 : 0 ≤ max (|s| - L) 0 := le_max_right _ _
  have key : (max (|s| - L) 0) ^ 2 ≤ ρ ↔ max (|s| - L) 0 ≤ √ρ := (Real.le_sqrt h0 hρ).symm
  rw [key, max_le_iff]
  have hsq := Real.sqrt_nonneg ρ
  constructor
  · rintro ⟨h1, -⟩
    have := abs_le.mp (show |s| ≤ L + √ρ by linarith)
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    have : |s| ≤ L + √ρ := abs_le.mpr ⟨by linarith, by linarith⟩
    exact ⟨by linarith, hsq⟩

-- its length: `2L` more than the slice of the ball, wherever the ball has one
theorem aux_slice_vol {L r : ℝ} (hL : 0 ≤ L) (w : Fin m → ℝ) :
    volume ((fun s : ℝ => (s, w)) ⁻¹' aux_P m L r)
      = {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2}.indicator (fun _ => ENNReal.ofReal (2 * L)) w
        + volume ((fun s : ℝ => (s, w)) ⁻¹' aux_P m 0 r) := by -- --- PROOF ---
  rw [aux_slice_eq, aux_slice_eq]
  by_cases hw : ∑ i, (w i) ^ 2 ≤ r ^ 2
  · have hρ : 0 ≤ r ^ 2 - ∑ i, (w i) ^ 2 := by linarith
    rw [indicator_of_mem (by exact hw), aux_slice_icc hρ, aux_slice_icc hρ, Real.volume_Icc,
      Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by
        have := Real.sqrt_nonneg (r ^ 2 - ∑ i, (w i) ^ 2); linarith)]
    congr 1
    ring
  · have hρ : r ^ 2 - ∑ i, (w i) ^ 2 < 0 := by linarith
    have hempty : ∀ L : ℝ, {s : ℝ | (max (|s| - L) 0) ^ 2 ≤ r ^ 2 - ∑ i, (w i) ^ 2} = ∅ := by
      intro L
      ext s
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hρ (sq_nonneg _)
    rw [indicator_of_notMem (by exact hw), hempty, hempty]
    simp


-- the cross-section ball is measurable too
theorem aux_meas_B (r : ℝ) : MeasurableSet {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2} :=
  measurableSet_le (by fun_prop) measurable_const

-- Fubini: the measure is `2L` times the cross-section plus the ball's
theorem aux_vol_P {L : ℝ} (r : ℝ) (hL : 0 ≤ L) :
    volume (aux_P m L r) = ENNReal.ofReal (2 * L) * volume {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2}
      + volume (aux_P m 0 r) := by -- --- PROOF ---
  have h1 := Measure.prod_apply_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin m → ℝ))) (aux_P_meas L r)
  have h0 := Measure.prod_apply_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin m → ℝ))) (aux_P_meas 0 r)
  rw [Measure.volume_eq_prod, h1, h0]
  simp_rw [aux_slice_vol hL]
  rw [lintegral_add_left (measurable_const.indicator (aux_meas_B r)),
    lintegral_indicator_const (aux_meas_B r)]


-- on the axis, the nearest point of the segment is found at a parameter in `[-1, 1]`
theorem aux_exists_t {s L : ℝ} (hL : 0 ≤ L) :
    ∃ t ∈ Icc (-1 : ℝ) 1, (s - t * L) ^ 2 = (max (|s| - L) 0) ^ 2 := by -- --- PROOF ---
  by_cases h1 : |s| ≤ L
  · have hmax : max (|s| - L) 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    by_cases hL0 : L = 0
    · subst hL0
      have : s = 0 := abs_nonpos_iff.mp h1
      exact ⟨0, ⟨by norm_num, by norm_num⟩, by simp [this]⟩
    · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
      refine ⟨s / L, ⟨?_, ?_⟩, by field_simp; ring⟩
      · rw [le_div_iff₀ hLp]; linarith [(abs_le.mp h1).1]
      · rw [div_le_iff₀ hLp]; linarith [(abs_le.mp h1).2]
  · rw [not_le] at h1
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs] at h1 ⊢
      refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [max_eq_left (by linarith)]; ring
    · rw [abs_of_neg hs] at h1 ⊢
      refine ⟨-1, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [max_eq_left (by linarith)]; ring

-- and no point of the segment is nearer
theorem aux_sq_le_of_mem {s L t : ℝ} (hL : 0 ≤ L) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (max (|s| - L) 0) ^ 2 ≤ (s - t * L) ^ 2 := by -- --- PROOF ---
  have h1 : |t * L| ≤ L := by
    rw [abs_mul, abs_of_nonneg hL]
    exact mul_le_of_le_one_left hL (abs_le.mpr ⟨ht.1, ht.2⟩)
  have h2 : |s| - L ≤ |s - t * L| := by
    have := abs_sub_abs_le_abs_sub s (t * L)
    have := abs_sub_abs_le_abs_sub (s - t * L) s
    have h3 : |s| ≤ |s - t * L| + |t * L| := by
      calc |s| = |(s - t * L) + t * L| := by ring_nf
        _ ≤ |s - t * L| + |t * L| := abs_add_le _ _
    linarith
  calc (max (|s| - L) 0) ^ 2 ≤ |s - t * L| ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) (max_le h2 (abs_nonneg _)) 2
    _ = (s - t * L) ^ 2 := sq_abs _


-- the Euclidean space, where the rotation lives
abbrev aux_E (m : ℕ) := EuclideanSpace ℝ (Fin (m + 1))

def aux_Kcap (g : aux_E m) (r : ℝ) : Set (aux_E m) := {y | ∃ t ∈ Icc (-1 : ℝ) 1, ‖y - t • g‖ ≤ r}

-- the coordinates `(first, rest)` of a vector, measure preservingly
def aux_Φ (m : ℕ) : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0

theorem aux_Φ_apply (v : Fin (m + 1) → ℝ) : aux_Φ m v = (v 0, fun i : Fin m => v i.succ) := rfl

-- on the first axis the capsule is the coordinate description
theorem aux_Kcap_axis {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) :
    aux_Kcap (L • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)) r
      = (fun y : aux_E m => aux_Φ m (WithLp.ofLp y)) ⁻¹' aux_P m L r := by -- --- PROOF ---
  ext y
  simp only [aux_Kcap, mem_setOf_eq, mem_preimage, aux_P, aux_Φ_apply]
  -- the squared distance from the axis point `t L e₀`, split at the first coordinate
  have hnorm : ∀ t : ℝ, ‖y - t • (L • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ))‖ ^ 2
      = (y 0 - t * L) ^ 2 + ∑ i : Fin m, (y i.succ) ^ 2 := by
    intro t
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
      Fin.sum_univ_succ]
    simp [Fin.succ_ne_zero]
  constructor
  · rintro ⟨t, ht, h⟩
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [hnorm] at h2
    have := aux_sq_le_of_mem (s := y 0) hL ht
    linarith
  · intro h
    obtain ⟨t, ht, he⟩ := aux_exists_t (s := y 0) hL
    refine ⟨t, ht, ?_⟩
    have h2 : ‖y - t • (L • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ))‖ ^ 2 ≤ r ^ 2 := by
      rw [hnorm, he]
      exact h
    exact le_of_sq_le_sq h2 hr |> fun h => h


-- a reflection takes the generator onto the first axis
theorem aux_exists_rot (g : aux_E m) :
    ∃ T : aux_E m ≃ₗᵢ[ℝ] aux_E m,
      T g = ‖g‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ) := by -- --- PROOF ---
  have h : ‖g‖ = ‖‖g‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)‖ := by
    rw [norm_smul, PiLp.norm_single]
    simp
  exact ⟨Submodule.reflection (ℝ ∙ (g - ‖g‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)))ᗮ,
    Submodule.reflection_sub h⟩

-- an isometry carries the capsule of `g` to that of its image
theorem aux_Kcap_rot (T : aux_E m ≃ₗᵢ[ℝ] aux_E m) (g : aux_E m) (r : ℝ) :
    aux_Kcap g r = T ⁻¹' aux_Kcap (T g) r := by
  ext y
  simp only [aux_Kcap, mem_setOf_eq, mem_preimage]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [← map_smul, ← map_sub, LinearIsometryEquiv.norm_map]

-- the coordinate description is measurable in the Euclidean space
theorem aux_meas_axis (L r : ℝ) :
    MeasurableSet ((fun y : aux_E m => aux_Φ m (WithLp.ofLp y)) ⁻¹' aux_P m L r) :=
  ((aux_Φ m).measurable.comp (PiLp.continuous_ofLp 2 (fun _ : Fin (m + 1) => ℝ)).measurable)
    (aux_P_meas L r)

-- and the coordinates preserve the measure
theorem aux_vol_axis (L r : ℝ) :
    volume ((fun y : aux_E m => aux_Φ m (WithLp.ofLp y)) ⁻¹' aux_P m L r)
      = volume (aux_P m L r) := by
  have hmp : MeasurePreserving (fun y : aux_E m => aux_Φ m (WithLp.ofLp y)) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (m + 1)))
  exact hmp.measure_preimage (aux_P_meas L r).nullMeasurableSet

-- the general capsule: rotate, then read off the measure
theorem aux_vol_Kcap (g : aux_E m) {r : ℝ} (hr : 0 ≤ r) :
    volume (aux_Kcap g r) = ENNReal.ofReal (2 * ‖g‖) *
        volume {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2}
      + volume (aux_Kcap (0 : aux_E m) r) := by -- --- PROOF ---
  obtain ⟨T, hT⟩ := aux_exists_rot g
  have h0 : volume (aux_Kcap (0 : aux_E m) r) = volume (aux_P m 0 r) := by
    have := aux_Kcap_axis (m := m) (le_refl 0) hr
    rw [zero_smul] at this
    rw [this, aux_vol_axis]
  have hmeas : MeasurableSet
      (aux_Kcap (‖g‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)) r) := by
    rw [aux_Kcap_axis (norm_nonneg g) hr]
    exact aux_meas_axis _ _
  rw [aux_Kcap_rot T g r, hT, T.measurePreserving.measure_preimage hmeas.nullMeasurableSet,
    aux_Kcap_axis (norm_nonneg g) hr, aux_vol_axis, aux_vol_P r (norm_nonneg g), h0]


-- every capsule is measurable, being a rotated axis one
theorem aux_meas_Kcap (g : aux_E m) {r : ℝ} (hr : 0 ≤ r) :
    MeasurableSet (aux_Kcap g r) := by
  obtain ⟨T, hT⟩ := aux_exists_rot g
  rw [aux_Kcap_rot T g r, hT, aux_Kcap_axis (norm_nonneg g) hr]
  exact T.continuous.measurable (aux_meas_axis _ _)

-- the ball constants, with `sqrt π` as a power of `π`
theorem aux_sqrtPi (k : ℕ) : Real.sqrt Real.pi ^ k = Real.pi ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  congr 1
  ring

-- the measure of the `n`-ball
theorem aux_vol_ball {r : ℝ} : -- --- STMT ---
    volume (aux_Kcap (0 : aux_E m) r)
      = ENNReal.ofReal r ^ (m + 1) *
        ENNReal.ofReal (Real.sqrt Real.pi ^ (m + 1)
          / Real.Gamma (((m + 1 : ℕ) : ℝ) / 2 + 1)) := by -- --- PROOF ---
  have h : aux_Kcap (0 : aux_E m) r
      = Metric.closedBall (0 : aux_E m) r := by
    ext y
    simp only [aux_Kcap, mem_setOf_eq, smul_zero, sub_zero, mem_closedBall_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, ⟨by norm_num, by norm_num⟩, h⟩⟩
  rw [h, EuclideanSpace.volume_closedBall (Fin (m + 1)) 0 r]
  simp

-- the measure of the `(n-1)`-ball, which is `1` for `n = 1`
theorem aux_vol_cyl {r : ℝ} (hr : 0 ≤ r) :
    volume {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2}
      = ENNReal.ofReal r ^ m *
        ENNReal.ofReal (Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hset : {w : Fin 0 → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2} = Set.univ := by
      ext w
      simp [sq_nonneg]
    rw [hset, volume_pi, Measure.pi_univ]
    simp
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hset : {w : Fin m → ℝ | ∑ i, (w i) ^ 2 ≤ r ^ 2}
      = (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r := by
    ext w
    simp only [mem_setOf_eq, mem_preimage, mem_closedBall_zero_iff, EuclideanSpace.norm_eq,
      Real.norm_eq_abs, sq_abs]
    exact (Real.sqrt_le_left hr).symm
  rw [hset, (PiLp.volume_preserving_toLp (Fin m)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall]
  simp

-- the capsule of `Capsule.construct` is the translate of the Euclidean one
theorem aux_construct_eq (C : Capsule (m + 1)) :
    C.construct = (fun x : Vec ℝ (m + 1) => -C.c + x) ⁻¹'
      ((WithLp.toLp 2) ⁻¹' aux_Kcap (WithLp.toLp 2 C.g : aux_E m) C.r) := by -- --- PROOF ---
  ext x
  simp only [Capsule.construct, aux_Kcap, mem_setOf_eq, mem_preimage]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [EuclideanSpace.norm_eq]
  have : ∀ i, ‖((WithLp.toLp 2 (-C.c + x) : aux_E m) - t • (WithLp.toLp 2 C.g : aux_E m)) i‖ ^ 2
      = (x i - (C.c i + t * C.g i)) ^ 2 := by
    intro i
    simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, PiLp.smul_apply]
    simp
    ring
  simp_rw [this]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.volume_eq {n : ℕ} (hn : 0 < n) (C : Capsule n) :
    MeasureTheory.volume C.construct = C.volume := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hr : C.r < 0
  · -- no point is within a negative radius
    have : C.construct = ∅ := by
      ext x
      simp only [Capsule.construct, mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists,
        not_and]
      intro t _
      exact not_le.mpr (lt_of_lt_of_le hr (Real.sqrt_nonneg _))
    rw [this, measure_empty]
    unfold Capsule.volume
    simp [hr]
  rw [not_lt] at hr
  -- translation, coordinates and rotation preserve the measure, leaving the two balls
  rw [aux_construct_eq, measure_preimage_add,
    (PiLp.volume_preserving_toLp (Fin (m + 1))).measure_preimage
      (aux_meas_Kcap _ hr).nullMeasurableSet,
    aux_vol_Kcap _ hr, aux_vol_cyl hr, aux_vol_ball]
  -- every factor is nonnegative, so the sum of products is one `ofReal`
  have hnorm : ‖(WithLp.toLp 2 C.g : aux_E m)‖ = Real.sqrt (∑ i, C.g i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have hΓ : ∀ x : ℝ, 0 < x → 0 < Real.Gamma x := fun x hx => Real.Gamma_pos_of_pos hx
  have hΓ0 : 0 < Real.Gamma ((m : ℝ) / 2 + 1) := hΓ _ (by positivity)
  have hΓ1 : 0 < Real.Gamma (((m + 1 : ℕ) : ℝ) / 2 + 1) := hΓ _ (by positivity)
  have hπ : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt (∑ i, C.g i ^ 2) := Real.sqrt_nonneg _
  unfold Capsule.volume
  rw [if_neg (by simp [not_lt.mpr hr]), hnorm,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [aux_sqrtPi, aux_sqrtPi]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.add_sub_cancel]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
