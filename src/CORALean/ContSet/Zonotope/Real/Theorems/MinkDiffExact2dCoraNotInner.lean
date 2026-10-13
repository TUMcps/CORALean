module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffExact2dCora
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# CORA's 2-D `minkDiff` returns a nonempty set where the difference is empty

For `Z = zonotope(0, eye(2))` and `Z₂ = zonotope(0, 2 * eye(2))`, `aux_areAligned` normalises both
generator matrices to `eye(2)` and accepts. The returned `zonotope(0, -eye(2))` is the unit
square, but `x + 2 [-1, 1]² ⊆ [-1, 1]²` has no solution: the subtrahend is the larger set.
So the `'exact'` result is not contained in the difference. The paper-side statement is
`Zonotope.minkDiffAligned_not_inner`; this is CORA's guard accepting every positive scaling.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffExact2dCora_not_inner :
    let Z₁ : Zonotope (Vec ℝ 2) := ⟨2, 0, fun j i => if i = j then 1 else 0⟩
    let Z₂ : Zonotope (Vec ℝ 2) := ⟨2, 0, fun j i => if i = j then 2 else 0⟩
    minkowskiDiff Z₁.construct Z₂.construct = ∅ ∧
      ∃ S, Z₁.minkDiffExact2dCora Z₂ = some S ∧ S.construct.Nonempty ∧
        ¬ S.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  intro Z₁ Z₂
  -- membership in `Z₁` bounds coordinate `0` by `1`
  have hmem : ∀ z ∈ Z₁.construct, |z 0| ≤ 1 := by
    rintro z ⟨β, hβ, hz⟩
    have h0 := congrFun hz 0
    simp [Z₁, Fin.sum_univ_two] at h0
    rw [h0]
    exact hβ 0
  -- `±2 e₀ ∈ Z₂`
  have hpm : ∀ s : ℝ, |s| ≤ 1 → (fun i => if i = 0 then 2 * s else 0 : Vec ℝ 2) ∈ Z₂.construct := by
    intro s hs
    refine ⟨fun j => if j = 0 then s else 0, fun j => ?_, ?_⟩
    · by_cases hj : j = 0 <;> simp [hj, hs]
    · funext i
      fin_cases i <;> simp [Z₂]; ring
  -- the difference is empty: `±2 e₀ ∈ Z₂` push coordinate `0` out of `[-1, 1]`
  have hempty : minkowskiDiff Z₁.construct Z₂.construct = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have h1 := abs_le.mp (hmem _ (hx _ (hpm 1 (by norm_num))))
    have h2 := abs_le.mp (hmem _ (hx _ (hpm (-1) (by norm_num))))
    simp at h1 h2
    linarith [h1.2, h2.1]
  -- `aux_areAligned` accepts: both column norms are constant (`1` and `2`), the quotients agree
  have hal : Z₁.areAlignedCora Z₂ rfl := by
    have e1 : ∀ j : Fin 2, Real.sqrt (∑ i : Fin 2, Z₁.G j i ^ 2) = 1 := by
      intro j
      fin_cases j <;> simp [Z₁]
    have e2 : ∀ j : Fin 2, Real.sqrt (∑ i : Fin 2, Z₂.G j i ^ 2) = 2 := by
      intro j
      fin_cases j <;> simp [Z₂]
    simp only [Zonotope.areAlignedCora, e1, e2, ciSup_const]
    norm_num
    intro j
    fin_cases j <;> simp [Z₁, Z₂]
  have hS : (Z₁.minkDiffAligned Z₂ rfl).c ∈ (Z₁.minkDiffAligned Z₂ rfl).construct :=
    ⟨fun _ => 0, fun _ => by simp, by simp⟩
  -- CORA returns the aligned closed form, whose centre lies in it, so it is nonempty and not `∅`
  refine ⟨hempty, Z₁.minkDiffAligned Z₂ rfl, ?_, ⟨_, hS⟩, ?_⟩
  · simp only [Zonotope.minkDiffExact2dCora]
    rw [dif_pos rfl, if_pos hal]
  · rw [hempty]
    exact fun h => h hS

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
