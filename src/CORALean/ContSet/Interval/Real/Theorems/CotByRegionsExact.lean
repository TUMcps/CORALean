module

public import CORALean.ContSet.Interval.Real.Operations.CotByRegions
public import CORALean.ContSet.Interval.Real.Theorems.ModSubModCases
public import CORALean.ContSet.Interval.Real.Theorems.TanUnboundedOfPole
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# `Interval.cotByRegions` is the cotangent's range, or its hull `]-∞, ∞[`

[1, Eq. 15] on any `lo ≤ hi` whose ends are not poles (`sin ≠ 0`): a finite result is the exact
range of the cotangent on `[lo, hi]`, its poles left out, and `]-∞, ∞[` comes exactly when a pole
lies inside, which makes the range unbounded both ways, so that `]-∞, ∞[` is its interval hull.
At an end on a pole the printed `[cot z̅, cot z̲]` is not the range: on `[π, 3π/2]` it reads
`[cot(π/2), cot 0]` while the range on `(π, 3π/2]` is `[0, ∞[`. Everything goes through
`cot x = tan(π/2 - x)`, so a pole of the cotangent inside is one of the tangent
(`Interval.tan_unbounded_of_pole`), and between two poles the cotangent falls.

## Inputs
* `lo` – lower end
* `hi` – upper end

## Hypotheses
* `hle` – lower end at most upper end
* `hlo` – sine nonzero at the lower end
* `hhi` – sine nonzero at the upper end

## Conclusion
* none means the cotangent is unbounded, else the interval is its exact range

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_cot_eq_tan (x : ℝ) : Real.cot x = Real.tan (Real.pi / 2 - x) := by
  rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, inv_div]

/-- The cotangent's values, poles left out, are the tangent's on the reflected range. -/
theorem aux_image_cot_eq (a b : ℝ) : -- --- CONCL ---
    Real.cot '' (Set.Icc a b ∩ {x | Real.sin x ≠ 0}) =
      Real.tan '' (Set.Icc (Real.pi / 2 - b) (Real.pi / 2 - a) ∩
        {x | Real.cos x ≠ 0}) := by -- --- PROOF ---
  ext v
  constructor
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    refine ⟨Real.pi / 2 - x, ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_setOf_eq, Real.cos_pi_div_two_sub]
    · rw [aux_cot_eq_tan]
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    refine ⟨Real.pi / 2 - x, ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_setOf_eq, ← Real.cos_pi_div_two_sub, sub_sub_cancel]
    · rw [aux_cot_eq_tan, sub_sub_cancel]

theorem aux_cot_sub_int_mul_pi (x : ℝ) (k : ℤ) : Real.cot (x - Real.pi * k) = Real.cot x := by
  rw [aux_cot_eq_tan, aux_cot_eq_tan, show Real.pi / 2 - (x - Real.pi * k) =
    Real.pi / 2 - x + k * Real.pi by ring, Real.tan_add_int_mul_pi]

/-- Between two consecutive poles of the tangent it rises: its range is the end values. -/
theorem aux_image_tan_between {c d : ℝ} (k : ℤ) (hcd : c ≤ d)
    (hc : -(Real.pi / 2) < c + k * Real.pi) (hd : d + k * Real.pi < Real.pi / 2) : -- --- CONCL ---
    Real.tan '' (Set.Icc c d ∩ {x | Real.cos x ≠ 0}) =
      Set.Icc (Real.tan c) (Real.tan d) := by -- --- PROOF ---
  have hin : ∀ x ∈ Set.Icc c d, x + k * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- no pole inside
  have hcos : ∀ x ∈ Set.Icc c d, Real.cos x ≠ 0 := fun x hx h0 => by
    have := Real.cos_pos_of_mem_Ioo (hin x hx)
    rw [Real.cos_add_int_mul_pi, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hset : Set.Icc c d ∩ {x | Real.cos x ≠ 0} = Set.Icc c d := Set.inter_eq_left.2 hcos
  have hmono : MonotoneOn Real.tan (Set.Icc c d) := fun x hx y hy hxy => by
    rw [← Real.tan_add_int_mul_pi x k, ← Real.tan_add_int_mul_pi y k]
    exact Real.strictMonoOn_tan.monotoneOn (hin x hx) (hin y hy) (by linarith)
  rw [hset, (Real.continuousOn_tan.mono fun x hx => hcos x hx).image_Icc_of_monotoneOn hcd hmono]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15], at ends that are not poles. -/
theorem Interval.cotByRegions_exact {lo hi : ℝ} (hle : lo ≤ hi) (hlo : Real.sin lo ≠ 0)
    (hhi : Real.sin hi ≠ 0) : -- --- CONCL ---
    (Interval.cotByRegions lo hi = none →
      ¬BddAbove (Real.cot '' (Set.Icc lo hi ∩ {x | Real.sin x ≠ 0})) ∧
        ¬BddBelow (Real.cot '' (Set.Icc lo hi ∩ {x | Real.sin x ≠ 0}))) ∧
    (∀ I, Interval.cotByRegions lo hi = some I →
      Real.cot
          '' (Set.Icc lo hi ∩ {x | Real.sin x ≠ 0}) = Set.Icc I.inf I.sup) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  simp only [Interval.cotByRegions]
  have hcases := fun hw => Interval.mod_sub_mod_cases hpi hle hw
  set zl := lo - Real.pi * ⌊lo / Real.pi⌋ with hzl_def
  set zu := hi - Real.pi * ⌊hi / Real.pi⌋ with hzu_def
  -- both reduced bounds in `(0, π)`, `0` being a pole
  have hred : ∀ x : ℝ, Real.sin x ≠ 0 → 0 < x - Real.pi * ⌊x / Real.pi⌋ ∧
      x - Real.pi * ⌊x / Real.pi⌋ < Real.pi := fun x hx => by
    have h1 : (⌊x / Real.pi⌋ : ℝ) ≤ x / Real.pi := Int.floor_le _
    have h2 : x / Real.pi < ⌊x / Real.pi⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hpi] at h1
    rw [div_lt_iff₀ hpi] at h2
    refine ⟨lt_of_le_of_ne (by nlinarith) fun h => hx ?_, by nlinarith⟩
    rw [show x = ⌊x / Real.pi⌋ * Real.pi by linarith, Real.sin_int_mul_pi]
  have hzl := hred lo hlo
  have hzu := hred hi hhi
  -- the next pole above `lo`, through the tangent
  have hpole : Real.cos (Real.pi / 2 - Real.pi * (⌊lo / Real.pi⌋ + 1)) = 0 := by
    rw [Real.cos_pi_div_two_sub, show Real.pi * (⌊lo / Real.pi⌋ + 1) =
      ((⌊lo / Real.pi⌋ + 1 : ℤ) : ℝ) * Real.pi by push_cast; ring, Real.sin_int_mul_pi]
  rw [aux_image_cot_eq]
  by_cases hw : Real.pi ≤ hi - lo
  · -- at least a period wide: a pole inside
    rw [if_pos (Or.inl hw)]
    refine ⟨fun _ => Interval.tan_unbounded_of_pole hpole (by linarith) (by linarith),
      fun I h => by cases h⟩
  split_ifs with hA
  · -- swapped: a pole inside
    have h := (hcases (not_le.1 hw)).resolve_left fun h => by linarith [h.1, hA.resolve_left hw]
    exact ⟨fun _ => Interval.tan_unbounded_of_pole hpole (by linarith) (by linarith [h.2]),
      fun I h => by cases h⟩
  · -- between two poles, falling
    refine ⟨fun h => (by cases h), fun I h => ?_⟩
    obtain rfl := Option.some.inj h
    dsimp only
    have h := (hcases (not_le.1 hw)).resolve_right fun h => hA (Or.inr h.1)
    rw [aux_image_tan_between ⌊lo / Real.pi⌋ (by linarith)
      (by linarith [h.2, hzu.2, hzl_def, hzu_def]) (by linarith [hzl.1]), ← aux_cot_eq_tan,
      ← aux_cot_eq_tan,
      ← aux_cot_sub_int_mul_pi hi ⌊hi / Real.pi⌋, ← aux_cot_sub_int_mul_pi lo ⌊lo / Real.pi⌋]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
