module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffConstruct
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# CORA's `conPolyZono/minkDiff` is not exact for a nonconvex minuend

`P = {-1, 1}` in `ℝ¹` (one factor `α` with the constraint `α² = 1`, generator `1`, exponent `1`) and
the zonotope `Z = [-1, 1]`. The test at the corners `x ± 1 ∈ P` passes for `x = 0`, so the result
contains `0`; but `0 + ½ ∉ P`, so `0 + Z ⊄ P` and `0 ∉ P ⊖ Z`. CORA labels this
computation `'exact'` and cites a theorem that assumes convexity. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result need not lie in the difference. -/
theorem ConPolyZono.minkDiff_not_inner :
    ∃ (cPZ : ConPolyZono (Vec ℝ 1)) (Z : Zonotope (Vec ℝ 1)),
      ¬ (cPZ.minkDiff Z).construct ⊆
        {x | ∀ z ∈ Z.construct, x + z ∈ cPZ.construct} := by -- --- PROOF ---
  -- `{α ∈ [-1, 1] | α² = 1}`, as the point `α`
  let cPZ : ConPolyZono (Vec ℝ 1) :=
    ⟨1, 1, 0, 1, 1, 0, fun _ => fun _ => 1, fun _ _ => 1, Fin.elim0, fun _ _ => 1,
      fun _ => 1, fun _ _ => 2⟩
  let Z : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
  refine ⟨cPZ, Z, fun h => ?_⟩
  -- every point of `P` is `±1`
  have hP : ∀ x ∈ cPZ.construct, x 0 = 1 ∨ x 0 = -1 := by
    rintro x ⟨a, β, ha, hβ, hs, rfl⟩
    have h1 := hs 0
    simp [PolyZonotope.monomial, cPZ, Matrix.mulVec, dotProduct] at h1
    rcases h1 with h3 | h3
    · left; simp [cPZ, PolyZonotope.monomial, h3]
    · right; simp [cPZ, PolyZonotope.monomial, h3]
  -- both `±1` are points of `P`
  have hmem : ∀ v : ℝ, v ^ 2 = 1 → |v| ≤ 1 → (fun _ => v : Vec ℝ 1) ∈ cPZ.construct := by
    intro v hv hv1
    refine ⟨fun _ => v, Fin.elim0, fun _ => hv1, fun j => j.elim0, ?_, ?_⟩
    · intro i
      simp [PolyZonotope.monomial, cPZ, Matrix.mulVec, dotProduct, hv]
    · funext k
      simp [cPZ, PolyZonotope.monomial]
  -- `0` passes the corner test
  have h0 : (fun _ => 0 : Vec ℝ 1) ∈ (cPZ.minkDiff Z).construct := by
    rw [ConPolyZono.minkDiff_construct]
    intro s
    simp only [Z, Fin.sum_univ_one, zero_add]
    cases hs : s 0
    · have e : ((fun _ => 0 : Vec ℝ 1) + -(fun _ => 1)) = fun _ => -1 := by
        funext k; simp
      simp only [Bool.false_eq_true, if_false]
      rw [e]
      exact hmem (-1) (by norm_num) (by norm_num)
    · have e : ((fun _ => 0 : Vec ℝ 1) + (fun _ => 1)) = fun _ => 1 := by
        funext k; simp
      simp only [if_true]
      rw [e]
      exact hmem 1 (by norm_num) (by norm_num)
  -- but `0 + ½ ∈ P` is false
  have := h h0 (fun _ => 1 / 2) ⟨fun _ => 1 / 2, fun _ => by norm_num, by funext k; simp [Z]⟩
  rcases hP _ this with h1 | h1 <;> norm_num at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
