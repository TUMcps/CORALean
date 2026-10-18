module

public import CORALean.ContSet.Conversion.Real.Operations.StarSet_to_ConZonotope
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A star set as a constrained zonotope

Exact when the factor box is not crossed, `l ≤ u`. The rescaling `α = mid + rad β` takes `|β| ≤ 1`
onto `[l, u]` and back, with `β = 0` where the box is a point, and carries each row to a halfspace
on `β`. A crossed box (`u < l`) denotes `∅`, which the rescaled factors, ranging over
`[mid - |rad|, mid + |rad|]`, would not.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to the rescaled factors is the rescaled row applied to them. -/
theorem StarSet.aux_row_rescale (s : StarSet StarSet.LinPred n) (a β : Fin s.m → ℝ) :
    ∑ k, a k * (((s.pred.l k + s.pred.u k) / 2) + ((s.pred.u k - s.pred.l k) / 2) * β k)
      = ∑ k, a k * ((s.pred.l k + s.pred.u k) / 2)
        + ∑ k, (a k * ((s.pred.u k - s.pred.l k) / 2)) * β k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.conZonotope_exact (s : StarSet StarSet.LinPred n)
    (hlu : ∀ k, s.pred.l k ≤ s.pred.u k) :
    s.conZonotope.construct = s.construct := by -- --- PROOF ---
  -- the point of the rescaled factors is the point of the original ones
  have hpt : ∀ (β : Fin s.m → ℝ) (x : Vec ℝ n),
      (x = s.conZonotope.c + ∑ j, β j • s.conZonotope.G j) ↔
        ∀ i, x i = s.c i + ∑ k, s.G i k *
          (((s.pred.l k + s.pred.u k) / 2) + ((s.pred.u k - s.pred.l k) / 2) * β k) :=
    fun β x => by
      simp only [funext_iff, StarSet.conZonotope, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      refine forall_congr' fun i => ?_
      rw [StarSet.aux_row_rescale, ← add_assoc]
      rw [Finset.sum_congr rfl fun k _ =>
        mul_comm (β k) (s.G i k * ((s.pred.u k - s.pred.l k) / 2))]
  -- the rows of the polytope on the coefficients, read off its definition
  have hev : ∀ (a β : Fin s.m → ℝ),
      (∑ k, a k • (LinearMap.proj k : (Fin s.m → ℝ) →ₗ[ℝ] ℝ)) β = ∑ k, a k * β k :=
    fun a β => by simp [Finset.sum_apply]
  have hA : ∀ (β : Fin s.m → ℝ) (i : Fin s.pred.cons.length),
      (β ∈ s.conZonotope.P.construct →
        ∑ k, ((s.pred.cons.get i).1 k * ((s.pred.u k - s.pred.l k) / 2)) * β k ≤
          (s.pred.cons.get i).2 - ∑ k, (s.pred.cons.get i).1 k * ((s.pred.l k + s.pred.u k) / 2)) :=
    fun β i hP => by
    have := hP.1 i
    change (∑ k, ((s.pred.cons.get i).1 k * ((s.pred.u k - s.pred.l k) / 2)) • LinearMap.proj k :
      Vec ℝ s.m →ₗ[ℝ] ℝ) β ≤ _ at this
    rwa [hev] at this
  ext x
  constructor
  · rintro ⟨β, hβ, hP, hx⟩
    refine ⟨fun k => (s.pred.l k + s.pred.u k) / 2 + (s.pred.u k - s.pred.l k) / 2 * β k,
      ⟨fun k => ?_, ?_⟩, (hpt β x).mp hx⟩
    · -- the box `[-1, 1]` is carried onto `[l, u]` by a nonnegative radius
      have h1 := abs_le.mp (hβ k)
      have hr : 0 ≤ (s.pred.u k - s.pred.l k) / 2 := by linarith [hlu k]
      constructor <;> nlinarith [mul_nonneg hr (by linarith [h1.1] : 0 ≤ β k + 1),
        mul_nonneg hr (by linarith [h1.2] : 0 ≤ 1 - β k)]
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
      rw [StarSet.aux_row_rescale]
      linarith [hA β i hP]
  · rintro ⟨α, ⟨hα, hrow⟩, hxα⟩
    -- the coefficients: the offset from the middle, in units of the radius
    set β : Fin s.m → ℝ := fun k =>
      if s.pred.u k - s.pred.l k = 0 then 0
      else (α k - (s.pred.l k + s.pred.u k) / 2) / ((s.pred.u k - s.pred.l k) / 2)
      with hβdef
    -- they rebuild the factors, also where the box is a point
    have hαβ : ∀ k, α k = (s.pred.l k + s.pred.u k) / 2 + (s.pred.u k - s.pred.l k) / 2 * β k := by
      intro k
      by_cases h0 : s.pred.u k - s.pred.l k = 0
      · simp only [hβdef, if_pos h0, h0]
        linarith [(hα k).1, (hα k).2]
      · -- otherwise the offset is a multiple of the radius
        simp only [hβdef, if_neg h0]
        field_simp
        ring
    have hα' : α = fun k => (s.pred.l k + s.pred.u k) / 2 + (s.pred.u k - s.pred.l k) / 2 * β k :=
      funext hαβ
    -- the coefficients are in the unit box, satisfy the rows, and give the point
    refine ⟨β, fun k => ?_, ⟨fun i => ?_, fun i => i.elim0⟩, (hpt β x).mpr fun i => ?_⟩
    · -- the coefficient is `0` at a point box, and within the radius otherwise
      by_cases h0 : s.pred.u k - s.pred.l k = 0
      · simp [hβdef, h0]
      · have hpos : 0 < (s.pred.u k - s.pred.l k) / 2 := by
          have := hlu k
          have : s.pred.u k - s.pred.l k ≠ 0 := h0
          positivity
        simp only [hβdef, if_neg h0]
        rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
        constructor <;> linarith [(hα k).1, (hα k).2]
    · have := hrow _ (List.get_mem _ i)
      rw [hα', StarSet.aux_row_rescale] at this
      show (∑ k, ((s.pred.cons.get i).1 k * ((s.pred.u k - s.pred.l k) / 2)) • LinearMap.proj k :
        Vec ℝ s.m →ₗ[ℝ] ℝ) β ≤
        (s.pred.cons.get i).2 - ∑ k, (s.pred.cons.get i).1 k * ((s.pred.l k + s.pred.u k) / 2)
      rw [hev]
      linarith
    · have := hxα i
      rw [hα'] at this
      exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
