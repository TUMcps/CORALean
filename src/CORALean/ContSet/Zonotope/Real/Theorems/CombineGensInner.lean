module

public import CORALean.ContSet.Zonotope.Real.Operations.CombineGens
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Combining two generators stays inside the zonotope

[1, Prop. 6]: `(G₁, c) ⊆ (G, c)` and `(G₂, c) ⊆ (G, c)`, since the segment along
`gᵢ ± gⱼ` lies in the sum of the segments along `gᵢ` and `gⱼ`. A coefficient `β` of the
new generator becomes `β` on `gᵢ` and `±β` on `gⱼ`; the others carry over.

## Inputs
* `Z` – zonotope
* `m` – generator count minus two
* `i` – first generator index
* `j` – second generator index among the rest
* `add` – sum if true, difference otherwise

## Hypotheses
* `hm` – generator count is `m + 2`

## Conclusion
* the combined zonotope lies in `Z`

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6]: replacing `gᵢ`, `gⱼ` by `gᵢ ± gⱼ` gives a subset. -/
theorem Zonotope.combineGens_inner (Z : Zonotope α) {m : ℕ} (hm : Z.h = m + 2)
    (i : Fin (m + 2)) (j : Fin (m + 1)) (add : Bool) :
    (Z.combineGens hm i j add).construct ⊆ Z.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  set s : ℝ := if add then 1 else -1 with hs
  have hs1 : |s| ≤ 1 := by rw [hs]; split_ifs <;> simp
  -- the coefficients over `Fin (m + 2)`: `β_new` at `i`, `s β_new` at `j`, the rest kept
  let δ : Fin (m + 2) → ℝ := Fin.insertNth i (β (Fin.last m))
    (Fin.insertNth j (s * β (Fin.last m)) fun k => β k.castSucc)
  refine ⟨fun l => δ (Fin.cast hm l), fun l => ?_, ?_⟩
  · -- every coefficient is one of `β`'s, possibly times `s`
    obtain ⟨l', rfl⟩ : ∃ l', Fin.cast hm.symm l' = l := ⟨Fin.cast hm l, by simp⟩
    simp only [Fin.cast_cast, Fin.cast_eq_self]
    rcases Fin.eq_self_or_eq_succAbove i l' with rfl | ⟨l₁, rfl⟩
    · simpa [δ] using hβ (Fin.last m)
    rcases Fin.eq_self_or_eq_succAbove j l₁ with rfl | ⟨l₂, rfl⟩
    · simpa [δ, abs_mul] using mul_le_one₀ hs1 (abs_nonneg _) (hβ (Fin.last m))
    · simpa [δ] using hβ l₂.castSucc
  · -- reindex `Z`'s sum onto `Fin (m + 2)`, then split off `i` and `j`
    have hre : ∑ l : Fin Z.h, δ (Fin.cast hm l) • Z.G l
        = ∑ l : Fin (m + 2), δ l • Z.G (Fin.cast hm.symm l) :=
      Equiv.sum_comp (finCongr hm) (fun l => δ l • Z.G (Fin.cast hm.symm l)) ▸ by simp
    rw [hre, Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
    -- the combined zonotope's sum, over `Fin (m + 1)` as its definition reads
    show Z.c + ∑ k : Fin (m + 1), β k • Fin.snoc (α := fun _ => α)
        (fun k : Fin m => Z.G (Fin.cast hm.symm (i.succAbove (j.succAbove k))))
        (if add then Z.G (Fin.cast hm.symm i) + Z.G (Fin.cast hm.symm (i.succAbove j))
          else Z.G (Fin.cast hm.symm i) - Z.G (Fin.cast hm.symm (i.succAbove j))) k = _
    rw [Fin.sum_univ_castSucc]
    simp only [δ, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.snoc_castSucc,
      Fin.snoc_last]
    rw [hs]
    cases add <;> simp only [Bool.false_eq_true, if_false, if_true] <;> module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
