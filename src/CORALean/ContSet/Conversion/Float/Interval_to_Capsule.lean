import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Real.Instances
import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe
import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Capsule
import CORALean.Global.Float.Sqrt

/-!
# A box as a capsule, over a floating-point scalar

CORA's `capsule(interval)`: the centre, the segment along a widest edge, and a ball thick enough
for the other half-widths. The stored centre and generator are rounded, and their distances from
the exact ones (`cGap`, `gGap`: the gap between the upward and downward roundings, per entry) are
added to the radius as lengths, with `‖hw‖₂` for the other half-widths, all rounded up
(`Global/Float/Sqrt`, `k` Newton steps).

The axis is chosen as CORA does, the first of maximal width, here by a left fold with `le` on the
rounded-up widths. The enclosure holds for every axis, so the choice affects only how tight the
capsule is, and the fold is computable. For `n = 0` there is no axis, and the capsule is the
point.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The capsule with the segment along axis `a`. -/
def Interval.capsuleAlong (k : ℕ) (I : Interval (Vec 𝕋 n)) (a : Fin n) : Capsule 𝕋 n :=
  let c := fun i => half (addDown (I.inf i) (I.sup i))
  let g := fun i => if i = a then half (subDown (I.sup i) (I.inf i)) else zero
  let cGap := fun i => subUp (half (addUp (I.inf i) (I.sup i))) (c i)
  let gGap := fun i =>
    if i = a then subUp (half (subUp (I.sup i) (I.inf i))) (half (subDown (I.sup i) (I.inf i)))
    else zero
  let hw := fun i => if i = a then zero else half (subUp (I.sup i) (I.inf i))
  ⟨c, g, addUp (addUp (normUp k hw) (normUp k cGap)) (normUp k gGap)⟩

/-- The first axis of maximal width, the widths rounded up. `none` exactly when `n = 0`. -/
def Interval.widestAxis (I : Interval (Vec 𝕋 n)) : Option (Fin n) :=
  (List.finRange n).foldl
    (fun best i =>
      match best with
      | none => some i
      | some b =>
        if le (subUp (I.sup i) (I.inf i)) (subUp (I.sup b) (I.inf b)) then some b else some i)
    none

/-- CORA's `capsule(interval)`. -/
def Interval.capsule (k : ℕ) (I : Interval (Vec 𝕋 n)) : Capsule 𝕋 n :=
  match I.widestAxis with
  | some a => I.capsuleAlong k a
  | none => ⟨fun _ => zero, fun _ => zero, zero⟩

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.capsuleAlong_contains (k : ℕ) (I : Interval (Vec 𝕋 n)) (a : Fin n) :
    I.construct ⊆ (I.capsuleAlong k a).construct := by -- --- PROOF ---
  intro x hx
  have hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i) := fun i =>
    le_trans (hx i).1 (hx i).2
  have hK := CORALean.Real.Interval.capsuleAlong_contains I.nominal a hx
  refine CORALean.Real.Capsule.construct_subset_of_dist_le (C := ⟨_, _, _⟩) ?_ hK
  -- the centre is within the gap of its two roundings
  have hc : ‖(fun i => (toReal (I.inf i) + toReal (I.sup i)) / 2) -
      toRealVec (fun i => half (addDown (I.inf i) (I.sup i)))‖₂ ≤
      toReal (normUp k fun i => subUp (half (addUp (I.inf i) (I.sup i)))
        (half (addDown (I.inf i) (I.sup i)))) := by
    refine norm₂_le_normUp k fun i => ?_
    have h₁ := addDown_le_add (I.inf i) (I.sup i)
    have h₂ := add_le_addUp (I.inf i) (I.sup i)
    have h₃ := sub_le_subUp (half (addUp (I.inf i) (I.sup i))) (half (addDown (I.inf i) (I.sup i)))
    simp only [toReal_half] at h₃
    show |(toReal (I.inf i) + toReal (I.sup i)) / 2 -
        toReal (half (addDown (I.inf i) (I.sup i)))| ≤ _
    simp only [toReal_half] at h₃ ⊢
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  -- the generator likewise, at the axis, and exactly zero elsewhere
  have hg : ‖(fun i => if i = a then (toReal (I.sup i) - toReal (I.inf i)) / 2 else 0) -
      toRealVec (fun i => if i = a then half (subDown (I.sup i) (I.inf i)) else zero)‖₂ ≤
      toReal (normUp k fun i => if i = a then subUp (half (subUp (I.sup i) (I.inf i)))
        (half (subDown (I.sup i) (I.inf i))) else zero) := by
    refine norm₂_le_normUp k fun i => ?_
    by_cases hia : i = a
    · subst hia
      simp only [Pi.sub_apply, toRealVec, if_true]
      have h₁ := subDown_le_sub (I.sup i) (I.inf i)
      have h₂ := sub_le_subUp (I.sup i) (I.inf i)
      have h₃ := sub_le_subUp (half (subUp (I.sup i) (I.inf i)))
        (half (subDown (I.sup i) (I.inf i)))
      simp only [toReal_half] at h₃ ⊢
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · simp only [Pi.sub_apply, toRealVec, hia, if_false]
      rw [toReal_zero]; simp
  -- the ball over the other axes is the length of the half-widths there
  have hr : Real.sqrt (∑ i, if i = a then 0 else ((toReal (I.sup i) - toReal (I.inf i)) / 2) ^ 2) ≤
      toReal (normUp k fun i => if i = a then zero else half (subUp (I.sup i) (I.inf i))) := by
    have : Real.sqrt (∑ i, if i = a then 0 else ((toReal (I.sup i) - toReal (I.inf i)) / 2) ^ 2) =
        ‖(fun i => if i = a then 0 else (toReal (I.sup i) - toReal (I.inf i)) / 2)‖₂ := by
      refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
      by_cases hia : i = a
      · simp [hia]
      · simp [hia]
    rw [this]
    refine norm₂_le_normUp k fun i => ?_
    by_cases hia : i = a
    · simp only [hia, if_true]; rw [toReal_zero]
    · simp only [hia, if_false]
      have h₂ := sub_le_subUp (I.sup i) (I.inf i)
      rw [toReal_half, abs_of_nonneg (by linarith [hI i]),
        abs_of_nonneg (by linarith [hI i])]
      linarith
  -- the three lengths, named, and their roundings added upward
  set A := normUp k fun i => if i = a then zero else half (subUp (I.sup i) (I.inf i)) with hA
  set B := normUp k fun i => subUp (half (addUp (I.inf i) (I.sup i)))
    (half (addDown (I.inf i) (I.sup i))) with hB
  set D := normUp k fun i => if i = a then subUp (half (subUp (I.sup i) (I.inf i)))
    (half (subDown (I.sup i) (I.inf i))) else zero with hD
  have s₁ := add_le_addUp A B
  have s₂ := add_le_addUp (addUp A B) D
  refine le_trans (add_le_add (add_le_add hc hg) hr) ?_
  have hfin : (I.capsuleAlong k a).nominal.r = toReal (addUp (addUp A B) D) := rfl
  rw [hfin]
  linarith

omit [SoundFloatArithmetic 𝕋] in
private theorem foldl_widest_some (I : Interval (Vec 𝕋 n)) :
    ∀ (l : List (Fin n)) (b : Fin n), ∃ b', l.foldl
      (fun best i =>
        match best with
        | none => some i
        | some b =>
          if le (subUp (I.sup i) (I.inf i)) (subUp (I.sup b) (I.inf b)) then some b else some i)
      (some b) = some b' := by -- --- PROOF ---
  intro l
  induction l with
  | nil => exact fun b => ⟨b, rfl⟩
  | cons i l ih =>
    intro b
    simp only [List.foldl_cons]
    split_ifs
    · exact ih b
    · exact ih i

theorem Interval.capsule_contains (k : ℕ) (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ (I.capsule k).construct := by -- --- PROOF ---
  unfold Interval.capsule
  cases h : I.widestAxis with
  | some a => exact I.capsuleAlong_contains k a
  | none =>
    have hn : n = 0 := by
      by_contra hn
      have hne : List.finRange n ≠ [] := by simpa [List.finRange_eq_nil_iff] using hn
      obtain ⟨i, l, hl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨b', hb'⟩ := foldl_widest_some I l i
      unfold Interval.widestAxis at h
      rw [hl, List.foldl_cons] at h
      simp only at h
      rw [hb'] at h
      simp at h
    subst hn
    intro x _
    exact ⟨0, by simp, by simp [Capsule.nominal, toReal_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
