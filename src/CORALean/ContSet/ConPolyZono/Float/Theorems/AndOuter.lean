import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact

/-!
# `ConPolyZono.and` over-approximates the intersection

The exact layer's `and_exact` read as an enclosure, and the first intersection
in this repository that a machine can run on non-convex sets.

The whole argument is that the stored data reads back to the exact layer's
`andDep` at *some* tolerance, and that the tolerance it reads back to is one the
two error boxes already fit inside. `aux_andD` is that tolerance — the stored
agreement interval minus the exact centre difference, which is what remains once
the rows have said what they say — and `aux_mem_andD` is the fitting.

The rounding therefore never has to be pushed anywhere: it is already inside the
interval the rows carry, because that interval was widened by two error boxes
before it was rounded at all.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## The constraint system read back -/

/-- The exact layer's tolerance the stored agreement interval amounts to: what
is left of it once the centre difference the rows also carry is subtracted. -/
def ConPolyZono.aux_andD (C₁ C₂ : ConPolyZono 𝕋 n) : Real.Interval (Vec ℝ n) :=
  ⟨fun i => toReal ((ConPolyZono.andAgree C₁ C₂).inf i)
      - (toReal (C₂.c i) - toReal (C₁.c i)),
   fun i => toReal ((ConPolyZono.andAgree C₁ C₂).sup i)
      - (toReal (C₂.c i) - toReal (C₁.c i))⟩

/-! Each read-back lemma first pins the exact layer's side in this layer's
spelling. Through `nominal` an index type reads `Fin ((nominal C₁).h + ..)`,
which `Fin.append_left` does not match even though it is the same type; the
`rfl` restatements say so once. -/

theorem ConPolyZono.toReal_agreeRow (C₁ C₂ : ConPolyZono 𝕋 n) (i : Fin n)
    (l : Fin (C₁.h + C₂.h)) :
    toReal (ConPolyZono.agreeRow C₁ C₂ i l)
      = Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) i l := by
  have hreal : Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) i
      = (Fin.append (fun l => toReal (C₁.G i l)) fun l => -toReal (C₂.G i l)) := rfl
  rw [hreal]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
    simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, toReal_neg]

-- the same restatement one level up, where `andA` stacks the two constraint blocks
theorem ConPolyZono.toRealMat_andA (C₁ C₂ : ConPolyZono 𝕋 n) :
    toRealMat (ConPolyZono.andA C₁ C₂)
      = Real.ConPolyZono.andA (nominal C₁) (nominal C₂) := by
  have hreal : Real.ConPolyZono.andA (nominal C₁) (nominal C₂)
      = fun i => Fin.append
          (fun r => Fin.append (Real.ConPolyZono.plusA (toRealMat C₁.A) (toRealMat C₂.A) r)
            (0 : Fin (C₁.h + C₂.h) → ℝ))
          (fun r => Fin.append (0 : Fin (C₁.s + C₂.s) → ℝ)
            (Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) r)) i := rfl
  rw [hreal]
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_) <;>
    refine funext (Fin.addCases (fun l => ?_) fun l => ?_)
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left]
    exact congrFun (congrFun (ConPolyZono.toRealMat_plusA C₁.A C₂.A) i) l
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_right]
    exact ConPolyZono.toReal_agreeRow C₁ C₂ i l

-- and the bounds, whose last block is the tolerance the agreement rows carry
theorem ConPolyZono.nominal_andB (C₁ C₂ : ConPolyZono 𝕋 n) :
    (ConPolyZono.andB C₁ C₂).nominal
      = Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.aux_andD C₁ C₂) := by
  have hreal : Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.aux_andD C₁ C₂)
      = (⟨Fin.append (Fin.append (toRealVec C₁.b.inf) (toRealVec C₂.b.inf))
            fun i => toReal (C₂.c i) - toReal (C₁.c i)
              + (ConPolyZono.aux_andD C₁ C₂).inf i,
          Fin.append (Fin.append (toRealVec C₁.b.sup) (toRealVec C₂.b.sup))
            fun i => toReal (C₂.c i) - toReal (C₁.c i)
              + (ConPolyZono.aux_andD C₁ C₂).sup i⟩ :
        Real.Interval (Vec ℝ (C₁.m + C₂.m + n))) := rfl
  have hinf : toRealVec (Fin.append (Fin.append C₁.b.inf C₂.b.inf)
        (ConPolyZono.andAgree C₁ C₂).inf)
      = Fin.append (Fin.append (toRealVec C₁.b.inf) (toRealVec C₂.b.inf))
        fun i => toReal (C₂.c i) - toReal (C₁.c i)
          + (ConPolyZono.aux_andD C₁ C₂).inf i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.aux_andD, toRealVec]
    ring
  -- the upper end, the same read-back with the other endpoint of each box
  have hsup : toRealVec (Fin.append (Fin.append C₁.b.sup C₂.b.sup)
        (ConPolyZono.andAgree C₁ C₂).sup)
      = Fin.append (Fin.append (toRealVec C₁.b.sup) (toRealVec C₂.b.sup))
        fun i => toReal (C₂.c i) - toReal (C₁.c i)
          + (ConPolyZono.aux_andD C₁ C₂).sup i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.aux_andD, toRealVec]
    ring
  rw [hreal]
  show (⟨toRealVec (Fin.append (Fin.append C₁.b.inf C₂.b.inf)
        (ConPolyZono.andAgree C₁ C₂).inf),
      toRealVec (Fin.append (Fin.append C₁.b.sup C₂.b.sup)
        (ConPolyZono.andAgree C₁ C₂).sup)⟩ :
    Real.Interval (Vec ℝ (C₁.m + C₂.m + n))) = _
  rw [hinf, hsup]

-- the whole record now, field by field, on the blocks just pinned
theorem ConPolyZono.nominal_andDep (C₁ C₂ : ConPolyZono 𝕋 n) :
    nominal (C₁.andDep C₂)
      = Real.ConPolyZono.andDep (nominal C₁) (nominal C₂) (ConPolyZono.aux_andD C₁ C₂) := by
  have hG : (fun (l : Fin (C₁.h + C₂.h)) (i : Fin n) =>
        toReal (Fin.append (C₁.G i) (fun _ => zero) l))
      = Fin.append (fun (l : Fin C₁.h) (i : Fin n) => toReal (C₁.G i l))
        (0 : Fin C₂.h → Vec ℝ n) := by
    refine funext (Fin.addCases (fun l => ?_) fun j => ?_) <;> funext i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  have hGI : (fun (j : Fin 0) (_ : Fin n) => toReal ((Fin.elim0 : Fin 0 → 𝕋) j))
      = (Fin.elim0 : Fin 0 → Vec ℝ n) := funext fun j => j.elim0
  -- the exact layer's record spelled out, so the field rewrites above have a term to match
  have hreal : Real.ConPolyZono.andDep (nominal C₁) (nominal C₂)
        (ConPolyZono.aux_andD C₁ C₂)
      = (⟨C₁.p + C₂.p, C₁.h + C₂.h, 0, C₁.m + C₂.m + n, C₁.s + C₂.s + (C₁.h + C₂.h),
        toRealVec C₁.c,
        Fin.append (fun (l : Fin C₁.h) (i : Fin n) => toReal (C₁.G i l))
          (0 : Fin C₂.h → Vec ℝ n),
        Real.PolyZonotope.plusE C₁.E C₂.E, (Fin.elim0 : Fin 0 → Vec ℝ n),
        Real.ConPolyZono.andA (nominal C₁) (nominal C₂),
        Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.aux_andD C₁ C₂),
        Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
          (Real.PolyZonotope.plusE C₁.E C₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) := rfl
  rw [hreal]
  -- and the float side in the same shape, so the two records differ only field by field
  show (⟨C₁.p + C₂.p, C₁.h + C₂.h, 0, C₁.m + C₂.m + n, C₁.s + C₂.s + (C₁.h + C₂.h),
      toRealVec C₁.c,
      fun l i => toReal (Fin.append (C₁.G i) (fun _ => zero) l),
      Real.PolyZonotope.plusE C₁.E C₂.E,
      fun j _ => toReal ((Fin.elim0 : Fin 0 → 𝕋) j),
      toRealMat (ConPolyZono.andA C₁ C₂), (ConPolyZono.andB C₁ C₂).nominal,
      Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
        (Real.PolyZonotope.plusE C₁.E C₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) = _
  rw [hG, hGI, ConPolyZono.toRealMat_andA, ConPolyZono.nominal_andB]

/-! ## The enclosure -/

/-- What the two error boxes let the two nominal points differ by, and the
tolerance the stored rows amount to covers it. -/
theorem ConPolyZono.aux_mem_andD (C₁ C₂ : ConPolyZono 𝕋 n) {e₁ e₂ : Vec ℝ n}
    (h₁ : e₁ ∈ C₁.err.construct) (h₂ : e₂ ∈ C₂.err.construct) :
    e₂ - e₁ ∈ (ConPolyZono.aux_andD C₁ C₂).construct := by
  intro i
  have hb₁ : toReal (C₁.err.inf i) ≤ e₁ i ∧ e₁ i ≤ toReal (C₁.err.sup i) := h₁ i
  have hb₂ : toReal (C₂.err.inf i) ≤ e₂ i ∧ e₂ i ≤ toReal (C₂.err.sup i) := h₂ i
  show (ConPolyZono.aux_andD C₁ C₂).inf i ≤ (e₂ - e₁) i
    ∧ (e₂ - e₁) i ≤ (ConPolyZono.aux_andD C₁ C₂).sup i
  rw [Pi.sub_apply]
  simp only [ConPolyZono.aux_andD, ConPolyZono.andAgree]
  constructor
  · linarith [addDown_le_add (subDown (C₂.c i) (C₁.c i))
      (subDown (C₂.err.inf i) (C₁.err.sup i)),
      subDown_le_sub (C₂.c i) (C₁.c i),
      subDown_le_sub (C₂.err.inf i) (C₁.err.sup i), hb₁.2, hb₂.1]
  · linarith [add_le_addUp (subUp (C₂.c i) (C₁.c i)) (subUp (C₂.err.sup i) (C₁.err.inf i)),
      sub_le_subUp (C₂.c i) (C₁.c i),
      sub_le_subUp (C₂.err.sup i) (C₁.err.inf i), hb₁.1, hb₂.2]

-- the nominal side is the exact layer's intersection, at the tolerance `aux_andD` supplies
theorem ConPolyZono.andDep_outer (C₁ C₂ : ConPolyZono 𝕋 n) (hq₁ : C₁.q = 0)
    (hq₂ : C₂.q = 0) : C₁.construct ∩ C₂.construct ⊆ (C₁.andDep C₂).construct := by
  have hnom : nominalSet (C₁.andDep C₂)
      = nominalSet C₁ ∩ (nominalSet C₂ + (ConPolyZono.aux_andD C₁ C₂).construct) := by
    show Real.ConPolyZono.construct (nominal (C₁.andDep C₂)) = _
    rw [ConPolyZono.nominal_andDep,
      ← Real.ConPolyZono.andDep_exact (nominal C₁) (nominal C₂) _ hq₁ hq₂]
    rfl
  -- one point, two decompositions: the nominal parts differ by exactly `e₂ - e₁`
  rintro x ⟨⟨y₁, hy₁, e₁, he₁, hx₁⟩, y₂, hy₂, e₂, he₂, hx₂⟩
  have hx₁' : y₁ + e₁ = x := hx₁
  have hx₂' : y₂ + e₂ = x := hx₂
  have hy : y₂ + (e₂ - e₁) = y₁ := by
    have h : y₂ + e₂ = y₁ + e₁ := hx₂'.trans hx₁'.symm
    have h' : y₂ + e₂ - e₁ = y₁ := by
      rw [h]
      abel
    calc y₂ + (e₂ - e₁) = y₂ + e₂ - e₁ := by abel
      _ = y₁ := h'
  exact ⟨y₁, hnom ▸ ⟨hy₁, y₂, hy₂, e₂ - e₁,
    ConPolyZono.aux_mem_andD C₁ C₂ he₁ he₂, hy⟩, e₁, he₁, hx₁⟩

theorem ConPolyZono.and_outer (C₁ C₂ : ConPolyZono 𝕋 n) :
    C₁.construct ∩ C₂.construct ⊆ (C₁.and C₂).construct := by
  rw [C₁.dependent_exact, C₂.dependent_exact]
  exact ConPolyZono.andDep_outer C₁.dependent C₂.dependent rfl rfl

end CORALean.Float
