module

public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Real.Theorems.CenterMemConstructIff

@[expose] public section

/-!
# A capsule is a point iff it has no direction and no radius

Needs `0 < n`: in dimension `0` the single point is also the capsule at any `r ≥ 0`. The
converse direction moves from the center along `g`, or by `r` along the first axis, to a second
point.

## Inputs
* `C` – capsule

## Hypotheses
* `hn` – positive dimension

## Conclusion
* `C = {C.c}` iff `representsa_point`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.representsa_point_iff (hn : 0 < n) (C : Capsule n) :
    C.construct = {C.c} ↔ C.representsa_point := by -- --- PROOF ---
  constructor
  · intro h
    -- the center is in the set, so `0 ≤ r`
    have hr0 : 0 ≤ C.r := (Capsule.center_mem_construct_iff C).mp (h ▸ rfl)
    have hg : C.g = 0 := by
      by_contra hg
      have hmem : C.c + C.g ∈ C.construct :=
        ⟨1, by norm_num, by simpa using hr0⟩
      rw [h] at hmem
      exact hg (add_eq_left.mp hmem)
    -- a nonzero radius leaves the center along the first axis
    refine ⟨hg, le_antisymm ?_ hr0⟩
    by_contra hr
    push Not at hr
    -- the point at distance `r` along the first axis
    set e : Vec ℝ n := Pi.single (⟨0, hn⟩ : Fin n) C.r with he
    have hmem : C.c + e ∈ C.construct := by
      refine ⟨0, by norm_num, ?_⟩
      have e1 : ∀ i, (C.c + e) i - (C.c i + 0 * C.g i) = e i := fun i => by simp
      show Real.sqrt (∑ i, ((C.c + e) i - (C.c i + 0 * C.g i)) ^ 2) ≤ C.r
      simp_rw [e1]
      have : ∑ i, e i ^ 2 = C.r ^ 2 := by simp [he, Pi.single_apply]
      rw [this, Real.sqrt_sq hr0]
    rw [h] at hmem
    have := add_eq_left.mp hmem
    have h2 := congrFun this ⟨0, hn⟩
    simp at h2
    exact hr.ne' h2
  · -- conversely the bound `‖x - c‖₂ ≤ 0` forces `x = c`
    rintro ⟨hg, hr⟩
    ext x
    constructor
    · rintro ⟨t, -, ht⟩
      simp only [hg, hr, Pi.zero_apply, mul_zero, add_zero, Set.mem_singleton_iff] at ht ⊢
      have hs : ∑ i, (x i - C.c i) ^ 2 = 0 := by
        refine le_antisymm ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        have := Real.sqrt_eq_zero'.mp (le_antisymm ht (Real.sqrt_nonneg _))
        exact this
      ext i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hs i (Finset.mem_univ _)
      linarith [pow_eq_zero_iff (two_ne_zero) |>.mp this]
    · rintro rfl
      exact ⟨0, by norm_num, by simp [hg, hr]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
