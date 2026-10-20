module

public import CORALean.ContSet.Conversion.Real.Operations.StarSet_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A star set as a constrained zonotope

Exact when the coefficient box is not crossed, `l ≤ u`. The rescaling `α = mid + rad β` takes `|β| ≤
1` onto `[l, u]` and back, with `β = 0` where the box is a point, and the predicate read at `α` is
the translated and pulled-back polytope read at `β`. A crossed box (`u < l`) denotes `∅`, which the
rescaled factors, ranging over `[mid - |rad|, mid + |rad|]`, would not.

## Inputs
* `s` – halfspace-predicate star set

## Hypotheses
* `hlu` – box ordered per coordinate

## Conclusion
* constrained zonotope equals the star set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to the rescaled factors is the rescaled row applied to them. -/
theorem StarSet.aux_row_rescale (s : StarSet ℋ𝒫 n) (a β : Fin s.m → ℝ) :
    ∑ k, a k * (((s.dom.inf k + s.dom.sup k) / 2) + ((s.dom.sup k - s.dom.inf k) / 2) * β k)
      = ∑ k, a k * ((s.dom.inf k + s.dom.sup k) / 2)
        + ∑ k, (a k * ((s.dom.sup k - s.dom.inf k) / 2)) * β k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.conZonotope_exact (s : StarSet ℋ𝒫 n)
    (hlu : ∀ k, s.dom.inf k ≤ s.dom.sup k) : -- --- CONCL ---
    s.conZonotope.construct = s.construct := by -- --- PROOF ---
  -- the middle and the radius of the box, and the rescaled factors
  set mid : Fin s.m → ℝ := fun k => (s.dom.inf k + s.dom.sup k) / 2 with hmid
  set rad : Fin s.m → ℝ := fun k => (s.dom.sup k - s.dom.inf k) / 2 with hrad
  -- the point of the rescaled factors is the point of the original ones
  have hpt : ∀ (β : Fin s.m → ℝ) (x : Vec ℝ n),
      (x = s.conZonotope.c + ∑ j, β j • s.conZonotope.G j) ↔
        ∀ i, x i = s.c i + ∑ k, s.G i k * (mid k + rad k * β k) :=
    fun β x => by
      simp only [funext_iff, StarSet.conZonotope, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      refine forall_congr' fun i => ?_
      rw [StarSet.aux_row_rescale, ← add_assoc]
      rw [Finset.sum_congr rfl fun k _ =>
        mul_comm (β k) (s.G i k * ((s.dom.sup k - s.dom.inf k) / 2))]
  -- the polytope on the coefficients is the predicate at the rescaled factors
  have hmem : ∀ β : Fin s.m → ℝ,
      β ∈ s.conZonotope.P.construct ↔ (fun k => mid k + rad k * β k) ∈ s.pred.construct := by
    intro β
    have hsc : (LinearMap.pi fun k => rad k • LinearMap.proj k : Vec ℝ s.m →ₗ[ℝ] Vec ℝ s.m) β
        = fun k => rad k * β k := by
      funext k
      simp
    show (LinearMap.pi fun k => rad k • LinearMap.proj k : Vec ℝ s.m →ₗ[ℝ] Vec ℝ s.m) β
      ∈ (s.pred.translate (-mid)).construct ↔ _
    -- the pulled-back point lies in the translate exactly when the rescaled one is in the predicate
    rw [hsc, ← HPolytope.translate_exact]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hy' : y = fun k => mid k + rad k * β k := funext fun k => by
        have := congrFun hyx k
        simp only [Pi.add_apply, Pi.neg_apply] at this
        linarith
      exact hy' ▸ hy
    · intro h
      exact ⟨_, h, funext fun k => by simp⟩
  ext x
  constructor
  · rintro ⟨β, hβ, hP, hx⟩
    refine ⟨fun k => mid k + rad k * β k, ⟨fun k => ?_, (hmem β).mp hP⟩, (hpt β x).mp hx⟩
    -- the box `[-1, 1]` is carried onto `[l, u]` by a nonnegative radius
    have h1 := abs_le.mp (hβ k)
    have hr : 0 ≤ rad k := by simp only [hrad]; linarith [hlu k]
    show s.dom.inf k ≤ mid k + rad k * β k ∧ mid k + rad k * β k ≤ s.dom.sup k
    simp only [hmid, hrad] at hr ⊢
    constructor <;> nlinarith [mul_nonneg hr (by linarith [h1.1] : 0 ≤ β k + 1),
      mul_nonneg hr (by linarith [h1.2] : 0 ≤ 1 - β k)]
  · rintro ⟨α, ⟨hα, hP⟩, hxα⟩
    -- the coefficients: the offset from the middle, in units of the radius
    set β : Fin s.m → ℝ := fun k => if rad k = 0 then 0 else (α k - mid k) / rad k with hβdef
    have hαk : ∀ k, s.dom.inf k ≤ α k ∧ α k ≤ s.dom.sup k := fun k => hα k
    -- they rebuild the factors, also where the box is a point
    have hαβ : ∀ k, α k = mid k + rad k * β k := by
      intro k
      by_cases h0 : rad k = 0
      · simp only [hβdef, if_pos h0, h0, zero_mul, add_zero]
        simp only [hrad, hmid] at h0 ⊢
        linarith [(hαk k).1, (hαk k).2]
      · -- otherwise the offset is a multiple of the radius
        simp only [hβdef, if_neg h0]
        field_simp
        ring
    have hα' : α = fun k => mid k + rad k * β k := funext hαβ
    -- the coefficients are in the unit box, satisfy the predicate, and give the point
    refine ⟨β, fun k => ?_, (hmem β).mpr (hα' ▸ hP), (hpt β x).mpr fun i => ?_⟩
    · -- the coefficient is `0` at a point box, and within the radius otherwise
      by_cases h0 : rad k = 0
      · simp [hβdef, h0]
      · have hpos : 0 < rad k := by
          have : 0 ≤ rad k := by simp only [hrad]; linarith [hlu k]
          exact lt_of_le_of_ne this (Ne.symm h0)
        simp only [hβdef, if_neg h0]
        rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
        simp only [hmid, hrad] at hpos ⊢
        constructor <;> linarith [(hαk k).1, (hαk k).2]
    · have := hxα i
      rw [hα'] at this
      exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
