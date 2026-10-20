module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitIndepGen
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `splitIndepGen` covers the set

A point with independent coefficient `βⱼ ≥ 0` is in the first half at `2βⱼ - 1`, one with
`βⱼ < 0` in the second at `2βⱼ + 1`; the halved generator is exact, and the center's rounding
`c ± g - cᵢ ≥ 0` is at most the gap added to the top of the error box.

## Inputs
* `pZ` – polynomial zonotope
* `j` – independent generator index

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The independent sum with generator `j` halved and coefficient `j` replaced by `b`. -/
theorem PolyZonotope.aux_sum_update (pZ : PolyZonotope (Vec 𝕋 n)) (j : Fin pZ.q) (β : Vec ℝ pZ.q)
    (b : ℝ) (i : Fin n) : -- --- CONCL ---
    ∑ k, toReal (Function.update pZ.GI j (fun i => half (pZ.GI j i)) k i)
        * Function.update β j b k
      = ∑ k, toReal (pZ.GI k i) * β k - toReal (pZ.GI j i) * β j
        + toReal (pZ.GI j i) / 2 * b := by -- --- PROOF ---
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _
    (Finset.mem_univ j)]
  simp only [Function.update_self, toReal_half]
  -- off `j` nothing changes
  have h : ∑ k ∈ Finset.univ.erase j, toReal (Function.update pZ.GI j
      (fun i => half (pZ.GI j i)) k i) * Function.update β j b k
      = ∑ k ∈ Finset.univ.erase j, toReal (pZ.GI k i) * β k :=
    Finset.sum_congr rfl fun k hk => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk),
        Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitIndepGen_outer (pZ : PolyZonotope (Vec 𝕋 n)) (j : Fin pZ.q) :
    pZ.construct ⊆
      (pZ.splitIndepGen j).1.construct ∪ (pZ.splitIndepGen j).2.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  have hb := abs_le.mp (hβ j)
  by_cases hj : 0 ≤ β j
  · -- the first half, at `2βⱼ - 1`, the center's rounding moved into the error
    left
    set d : Vec ℝ n := fun i => toReal (pZ.c i) + toReal (pZ.GI j i) / 2
      - toReal (addDown (pZ.c i) (half (pZ.GI j i)))
    refine ⟨z - d, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Function.update β j (2 * β j - 1), ha,
      fun k => ?_, fun i => ?_⟩, e + d, fun i => ⟨?_, ?_⟩, by ring⟩
    · -- the new coefficient is in `[-1, 1]`
      by_cases hk : k = j
      · rw [hk, Function.update_self]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [Function.update_of_ne hk]; exact hβ k
    · show z i - d i = toReal (addDown (pZ.c i) (half (pZ.GI j i)))
        + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l
        + ∑ k, toReal (Function.update pZ.GI j (fun i => half (pZ.GI j i)) k i)
          * Function.update β j (2 * β j - 1) k
      rw [hz i, PolyZonotope.aux_sum_update]
      simp only [d]
      ring
    · have hd : 0 ≤ d i := by
        have := addDown_le_add (pZ.c i) (half (pZ.GI j i))
        simp only [d, toReal_half] at this ⊢
        linarith
      have he1 : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
      show toReal (pZ.I_error.inf i) ≤ e i + d i
      linarith
    · -- the rounding gap bounds `d` above
      have hgap := sub_le_subUp (addUp (pZ.c i) (half (pZ.GI j i)))
        (addDown (pZ.c i) (half (pZ.GI j i)))
      have hup := add_le_addUp (pZ.c i) (half (pZ.GI j i))
      have hsum := add_le_addUp (pZ.I_error.sup i) (subUp (addUp (pZ.c i) (half (pZ.GI j i)))
        (addDown (pZ.c i) (half (pZ.GI j i))))
      show e i + d i ≤ toReal (addUp (pZ.I_error.sup i) (subUp (addUp (pZ.c i) (half (pZ.GI j i)))
        (addDown (pZ.c i) (half (pZ.GI j i)))))
      have he2 : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
      simp only [d, toReal_half] at hup ⊢
      linarith
  · -- the second half, at `2βⱼ + 1`
    right
    replace hj := lt_of_not_ge hj
    set d : Vec ℝ n := fun i => toReal (pZ.c i) - toReal (pZ.GI j i) / 2
      - toReal (subDown (pZ.c i) (half (pZ.GI j i)))
    refine ⟨z - d, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Function.update β j (2 * β j + 1), ha,
      fun k => ?_, fun i => ?_⟩, e + d, fun i => ⟨?_, ?_⟩, by ring⟩
    · -- the new coefficient is in `[-1, 1]`
      by_cases hk : k = j
      · rw [hk, Function.update_self]; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [Function.update_of_ne hk]; exact hβ k
    · show z i - d i = toReal (subDown (pZ.c i) (half (pZ.GI j i)))
        + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l
        + ∑ k, toReal (Function.update pZ.GI j (fun i => half (pZ.GI j i)) k i)
          * Function.update β j (2 * β j + 1) k
      rw [hz i, PolyZonotope.aux_sum_update]
      simp only [d]
      ring
    · have hd : 0 ≤ d i := by
        have := subDown_le_sub (pZ.c i) (half (pZ.GI j i))
        simp only [d, toReal_half] at this ⊢
        linarith
      have he1 : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
      show toReal (pZ.I_error.inf i) ≤ e i + d i
      linarith
    · -- the rounding gap bounds `d` above
      have hgap := sub_le_subUp (subUp (pZ.c i) (half (pZ.GI j i)))
        (subDown (pZ.c i) (half (pZ.GI j i)))
      have hup := sub_le_subUp (pZ.c i) (half (pZ.GI j i))
      have hsum := add_le_addUp (pZ.I_error.sup i) (subUp (subUp (pZ.c i) (half (pZ.GI j i)))
        (subDown (pZ.c i) (half (pZ.GI j i))))
      show e i + d i ≤ toReal (addUp (pZ.I_error.sup i) (subUp (subUp (pZ.c i) (half (pZ.GI j i)))
        (subDown (pZ.c i) (half (pZ.GI j i)))))
      have he2 : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
      simp only [d, toReal_half] at hup ⊢
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
