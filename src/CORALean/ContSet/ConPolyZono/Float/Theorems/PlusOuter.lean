import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

/-!
# `ConPolyZono.plus` over-approximates the Minkowski sum

`PolyZonotope.plus_outer`'s argument at one more field. What the constraint
block needs is that the exact layer's `holds_plus_iff` still applies once the
stored floats are read as reals — which it does, because `plusA` copies entries
and writes `zero` in the off-blocks, so reading it back is the exact layer's
`plusA` of the two read-back matrices. `toRealMat_plusA` is that statement, and
it is the whole price of carrying constraints across the layer.

Only the centre rounds, so the box holds the two incoming boxes and one
`centerResidual`, and all five counts are the exact layer's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## The constraint system read back -/

theorem ConPolyZono.toRealMat_plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat 𝕋 m₁ s₁)
    (A₂ : Mat 𝕋 m₂ s₂) :
    toRealMat (ConPolyZono.plusA A₁ A₂)
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) := by
  have key : ∀ i l, toRealMat (ConPolyZono.plusA A₁ A₂) i l
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) i l := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) <;>
      simp only [toRealMat, ConPolyZono.plusA, Real.ConPolyZono.plusA,
        Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  exact funext fun i => funext fun l => key i l

theorem ConPolyZono.toRealVec_append {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) :
    toRealVec (Fin.append b₁ b₂) = Fin.append (toRealVec b₁) (toRealVec b₂) := by
  refine funext (Fin.addCases (fun i => ?_) (fun i => ?_)) <;>
    simp only [toRealVec, Fin.append_left, Fin.append_right]

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with — the exact layer's lemma, at the read-back data. -/
theorem ConPolyZono.satisfies_plus_iff (C₁ C₂ : ConPolyZono 𝕋 n)
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.plus C₂).satisfies a
      ↔ C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)) := by
  show Real.ConPolyZono.holds (toRealMat (ConPolyZono.plusA C₁.A C₂.A))
      (toRealVec (Fin.append C₁.b C₂.b)) (Real.PolyZonotope.plusE C₁.EC C₂.EC) a ↔ _
  rw [ConPolyZono.toRealMat_plusA, ConPolyZono.toRealVec_append]
  exact Real.ConPolyZono.holds_plus_iff _ _ _ _ _ _ a

/-! ## The enclosure -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem ConPolyZono.plus_h (C₁ C₂ : ConPolyZono 𝕋 n) :
    (C₁.plus C₂).h = C₁.h + C₂.h := rfl

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem ConPolyZono.aux_sum_univ_plus_h {C₁ C₂ : ConPolyZono 𝕋 n}
    (f : Fin (C₁.h + C₂.h) → ℝ) :
    ∑ l : Fin (C₁.plus C₂).h, f l
      = ∑ l, f (Fin.castAdd C₂.h l) + ∑ l, f (Fin.natAdd C₁.h l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent generator count. -/
theorem ConPolyZono.aux_sum_univ_plus_q {C₁ C₂ : ConPolyZono 𝕋 n}
    (f : Fin (C₁.q + C₂.q) → ℝ) :
    ∑ j : Fin (C₁.plus C₂).q, f j
      = ∑ j, f (Fin.castAdd C₂.q j) + ∑ j, f (Fin.natAdd C₁.q j) :=
  Fin.sum_univ_add f

theorem ConPolyZono.aux_plus_nominal (C₁ C₂ : ConPolyZono 𝕋 n) :
    nominalSet C₁ + nominalSet C₂ ⊆
      nominalSet (C₁.plus C₂) + (PolyZonotope.centerResidual C₁.c C₂.c).construct := by
  rintro _ ⟨x₁, hx₁', x₂, hx₂', rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hs₁, hx₁⟩ := ConPolyZono.mem_nominalSet_iff.mp hx₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hs₂, hx₂⟩ := ConPolyZono.mem_nominalSet_iff.mp hx₂'
  have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd C₂.p k)) = a₁ :=
    funext fun k => Fin.append_left a₁ a₂ k
  have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd C₁.p k)) = a₂ :=
    funext fun k => Fin.append_right a₁ a₂ k
  refine ⟨fun i => toReal ((C₁.plus C₂).c i)
            + (∑ l, toReal ((C₁.plus C₂).G i l)
                * Real.PolyZonotope.monomial (C₁.plus C₂).E (Fin.append a₁ a₂) l)
            + ∑ j, toReal ((C₁.plus C₂).GI i j) * Fin.append β₁ β₂ j,
          ConPolyZono.mem_nominalSet_iff.mpr
            ⟨Fin.append a₁ a₂, Fin.append β₁ β₂, ?_, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (C₁.c i) + toReal (C₂.c i) - toReal ((C₁.plus C₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa using ha₁ k
    · simpa using ha₂ k
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · simpa using hβ₁ j
    · simpa using hβ₂ j
  · refine (ConPolyZono.satisfies_plus_iff C₁ C₂ _).mpr ⟨?_, ?_⟩
    · rw [hA₁]; exact hs₁
    · rw [hA₂]; exact hs₂
  · exact Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Pi.add_apply]
    rw [ConPolyZono.aux_sum_univ_plus_h, ConPolyZono.aux_sum_univ_plus_q]
    simp only [ConPolyZono.plus, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
      hx₁ i, hx₂ i]
    ring

/-- The box absorbs the two incoming boxes and the centre rounding. -/
theorem ConPolyZono.aux_plus_error (C₁ C₂ : ConPolyZono 𝕋 n) :
    C₁.err.construct + C₂.err.construct
        + (PolyZonotope.centerResidual C₁.c C₂.c).construct ⊆ (C₁.plus C₂).err.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer C₁.err C₂.err))
    (Interval.plus_outer _ _)

theorem ConPolyZono.plus_outer (C₁ C₂ : ConPolyZono 𝕋 n) :
    C₁.construct + C₂.construct ⊆ (C₁.plus C₂).construct :=
  InflatedContSet.plus_subset (ConPolyZono.aux_plus_nominal C₁ C₂)
    (ConPolyZono.aux_plus_error C₁ C₂)

end CORALean.Float
