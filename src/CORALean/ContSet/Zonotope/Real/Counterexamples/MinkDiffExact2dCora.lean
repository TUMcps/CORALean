module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `Zonotope.IsAlignedCora`, CORA's `aux_areAligned`

CORA's `@zonotope/minkDiff.m` [1], `aux_areAligned` (l. 522-549): the generator matrices must have
the same size; if both are zero the sets are aligned, if exactly one is zero they are not;
otherwise both matrices are divided by their largest column 2-norm (`vecnorm`, l. 530-531,
`max`) and compared column by column, in order, up to `eps` (l. 542).

The comparison is an equality of the two normalised matrices, so it accepts a subtrahend
that is ANY positive multiple of the minuend, in particular a larger one. The `IsWithinTol` and
`eps` tolerances are read as exact equality here.

# `Zonotope.minkDiffExact2dCora`, CORA's two-dimensional `minkDiff`

CORA's `@zonotope/minkDiff.m` on a full-dimensional 2-D minuend whose subtrahend has
generators. l. 117-120 force `method = 'exact'` for `n == 2`, so every call (the default
`'approx'` included) reaches l. 123: if `aux_areAligned` holds, l. 125 returns
`zonotope(minuend.c - subtrahend.c, minuend.G - subtrahend.G)` ("exact solution for aligned sets
according to [2, Prop. 5]"). Otherwise l. 127 calls `aux_minkDiffZono`, which is not modelled
here: `none`. The header documents `'exact'` as the exact difference.

# CORA's 2-D `minkDiff` returns a nonempty set where the difference is empty

For `Z = zonotope(0, eye(2))` and `Z₂ = zonotope(0, 2 * eye(2))`, `aux_areAligned` normalises both
generator matrices to `eye(2)` and accepts. The returned `zonotope(0, -eye(2))` is the unit
square, but `x + 2 [-1, 1]² ⊆ [-1, 1]²` has no solution: the subtrahend is the larger set.
So the `'exact'` result is not contained in the difference. The paper-side statement is
`Zonotope.minkDiffAligned_not_inner`; this is CORA's guard accepting every positive scaling.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's result is not inside the true Minkowski difference

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 522-549.
* [2] `contSet/@zonotope/minkDiff.m`, CORA, ll. 117-127.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `aux_areAligned(minuend, subtrahend)` once the sizes agree (`hh`, l. 530's size test). -/
def Zonotope.IsAlignedCora (minuend subtrahend : Zonotope (Vec ℝ n))
    (hh : minuend.h = subtrahend.h) : Prop :=
  -- l. 530: `normMin = max(vecnorm(Gmin))`
  let normMin : ℝ := ⨆ j, Real.sqrt (∑ i, minuend.G j i ^ 2)
  -- l. 531: `normSub = max(vecnorm(Gsub))`
  let normSub : ℝ := ⨆ j, Real.sqrt (∑ i, subtrahend.G j i ^ 2)
  if normMin = 0 ∧ normSub = 0 then True
  else if normMin = 0 ∨ normSub = 0 then False
  else ∀ j i, minuend.G j i / normMin = subtrahend.G (Fin.cast hh j) i / normSub

end CORALean.Real

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- The aligned branch of the forced `'exact'` path; `none` is `aux_minkDiffZono` (not modelled). -/
noncomputable def Zonotope.minkDiffExact2dCora (minuend subtrahend : Zonotope (Vec ℝ 2)) :
    Option (Zonotope (Vec ℝ 2)) :=
  if hh : minuend.h = subtrahend.h then
    -- l. 123: `if aux_areAligned(minuend, subtrahend)`
    if minuend.IsAlignedCora subtrahend hh then
      -- l. 125: `zonotope(minuend.c - subtrahend.c, minuend.G - subtrahend.G)`
      some (minuend.minkDiffAligned subtrahend hh)
    else none
  else none


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffExact2dCora_not_inner : -- --- CONCL ---
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
  have hal : Z₁.IsAlignedCora Z₂ rfl := by
    have e1 : ∀ j : Fin 2, Real.sqrt (∑ i : Fin 2, Z₁.G j i ^ 2) = 1 := by
      intro j
      fin_cases j <;> simp [Z₁]
    have e2 : ∀ j : Fin 2, Real.sqrt (∑ i : Fin 2, Z₂.G j i ^ 2) = 2 := by
      intro j
      fin_cases j <;> simp [Z₂]
    simp only [Zonotope.IsAlignedCora, e1, e2, ciSup_const]
    norm_num
    intro j
    fin_cases j <;> simp [Z₁, Z₂]
  have hS : (Z₁.minkDiffAligned Z₂ rfl).c ∈ (Z₁.minkDiffAligned Z₂ rfl).construct :=
    ⟨fun _ => 0, fun _ => by simp, by simp⟩
  -- CORA returns the aligned closed form, whose center lies in it, so it is nonempty and not `∅`
  refine ⟨hempty, Z₁.minkDiffAligned Z₂ rfl, ?_, ⟨_, hS⟩, ?_⟩
  · simp only [Zonotope.minkDiffExact2dCora]
    rw [dif_pos rfl, if_pos hal]
  · rw [hempty]
    exact fun h => h hS

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
