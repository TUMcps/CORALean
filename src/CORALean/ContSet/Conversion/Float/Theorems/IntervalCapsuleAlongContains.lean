module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalCapsuleAlongContains
public import CORALean.Global.Float.Sqrt
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.SmulMemSymmetric

@[expose] public section

/-!
# A box as a capsule, over a floating-point scalar

CORA's `capsule(interval)`: the center, the segment along a widest edge, and a ball thick enough
for the other half-widths. The stored center and generator are rounded, and what they miss of the
exact ones (between the upward and downward roundings, per entry) is in the error box: the
center's in the residual box, the generator's, at the segment parameter, in the symmetric box of
its gap. The radius is `‖hw‖₂` for the other half-widths, rounded up (`Global/Float/Sqrt`, `k`
Newton steps).

The axis is chosen as CORA does, the first of maximal width, here by a left fold with `le` on the
rounded-up widths. The enclosure holds for every axis, so the choice affects only how tight the
capsule is, and the fold is computable. For `n = 0` there is no axis, and the capsule is the
point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.capsuleAlong_contains (k : ℕ) (I : Interval (Vec 𝕋 n)) (a : Fin n) :
    I.construct ⊆ (I.capsuleAlong k a).construct := by -- --- PROOF ---
  intro x hx
  have hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i) := fun i =>
    le_trans (hx i).1 (hx i).2
  have hK := CORALean.Real.Interval.capsuleAlong_contains I.nominal a hx
  obtain ⟨t, ht, w, hw, rfl⟩ := Capsule.exists_split_of_mem hK
  refine Capsule.mem_construct_of_split _ ht (w := w) ?_ ?_
  · -- the ball over the other axes is the length of the half-widths there
    refine le_trans hw ?_
    have : Real.sqrt (∑ i, if i = a then 0 else ((toReal (I.sup i) - toReal (I.inf i)) / 2) ^ 2) =
        ‖(fun i => if i = a then 0 else (toReal (I.sup i) - toReal (I.inf i)) / 2)‖₂ := by
      refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
      by_cases hia : i = a
      · simp [hia]
      · simp [hia]
    show Real.sqrt (∑ i, if i = a then 0 else ((toReal (I.sup i) - toReal (I.inf i)) / 2) ^ 2) ≤ _
    rw [this]
    refine norm₂_le_normUp k fun i => ?_
    by_cases hia : i = a
    · simp only [hia, if_true]; rw [toReal_zero]
    · simp only [hia, if_false]
      have h₂ := sub_le_subUp (I.sup i) (I.inf i)
      rw [toReal_half, abs_of_nonneg (by linarith [hI i]),
        abs_of_nonneg (by linarith [hI i])]
      linarith
  · -- the center is between its two roundings
    have hc := Interval.sub_mem_residual (stored := fun i => half (addDown (I.inf i) (I.sup i)))
      (x := fun i => (toReal (I.inf i) + toReal (I.sup i)) / 2)
      (lo := fun i => half (addDown (I.inf i) (I.sup i)))
      (hi := fun i => half (addUp (I.inf i) (I.sup i))) fun i => by
        have h₁ := addDown_le_add (I.inf i) (I.sup i)
        have h₂ := add_le_addUp (I.inf i) (I.sup i)
        simp only [toReal_half]
        constructor <;> linarith
    -- the generator likewise, at the axis, and exactly zero elsewhere
    have hg := Capsule.smul_mem_symmetric (t := t)
      (m := fun i => if i = a then subUp (half (subUp (I.sup i) (I.inf i)))
        (half (subDown (I.sup i) (I.inf i))) else zero)
      (δ := (fun i => if i = a then (toReal (I.sup i) - toReal (I.inf i)) / 2 else 0) -
        toRealVec (fun i => if i = a then half (subDown (I.sup i) (I.inf i)) else zero)) ht
      fun i => by
        by_cases hia : i = a
        · subst hia
          simp only [Pi.sub_apply, toRealVec, if_true]
          have h₁ := subDown_le_sub (I.sup i) (I.inf i)
          have h₂ := sub_le_subUp (I.sup i) (I.inf i)
          have h₃ := sub_le_subUp (half (subUp (I.sup i) (I.inf i)))
            (half (subDown (I.sup i) (I.inf i)))
          simp only [toReal_half] at h₃ ⊢
          rw [abs_of_nonneg (by linarith)]
          linarith
        · simp only [Pi.sub_apply, toRealVec, hia, if_false]
          rw [toReal_zero]; simp
    -- the two summed into the stored box, and the difference is their sum
    show _ ∈ ((Interval.residual (fun i => half (addDown (I.inf i) (I.sup i)))
      (fun i => half (addUp (I.inf i) (I.sup i)))
      (fun i => half (addDown (I.inf i) (I.sup i)))).plus
      (Interval.symmetric fun i => if i = a then subUp (half (subUp (I.sup i) (I.inf i)))
        (half (subDown (I.sup i) (I.inf i))) else zero)).construct
    convert Interval.plus_outer _ _ ⟨_, hc, _, hg, rfl⟩ using 1
    funext i
    simp only [CORALean.Real.Interval.capsuleAlong, Interval.capsuleAlong, Interval.nominal,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    show ((toReal (I.inf i) + toReal (I.sup i)) / 2 +
      t * if i = a then (toReal (I.sup i) - toReal (I.inf i)) / 2 else 0) + _ - _ = _
    by_cases hia : i = a
    · simp only [hia, if_true, toRealVec]
      ring
    · simp only [hia, if_false, toRealVec]
      ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
