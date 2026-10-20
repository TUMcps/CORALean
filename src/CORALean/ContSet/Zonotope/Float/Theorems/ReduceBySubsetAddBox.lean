module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `reduceBy` reaches no further than its operand plus `reduceByBox`

The reverse of `reduceBy_outer`, and `Real`'s own `reduceBy_subset_add_box` argument carried across,
now computed in `𝕋`: the kept coefficients read back onto `Z`, the dropped ones set to `0`, and what
is left is the diagonal block, rounded up via `radius`, which is also what `reduceBy`'s own diagonal
block stores, so the two match exactly. `reduceByBox`'s own error box is degenerately `0`.
`reduceBy` never touches the box (`I_error := Z.I_error`), so `y₂` witnesses membership in `Z`'s own
error box directly, with no `0`-in-the-box hypothesis as `plus` and `mtimes` need.

## Inputs
* `Z` – zonotope
* `part` – split into kept and reduced generators

## Hypotheses
* none

## Conclusion
* reduction is contained in the zonotope plus the reduction box
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_reduceBy_box {Z : Zonotope (Vec 𝕋 n)}
    {part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceBy part).h, f j = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reduceBy` reaches no further than `Z.construct` widened by `reduceByBox`. -/
theorem Zonotope.reduceBy_subset_add_box (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : -- --- CONCL ---
    (Z.reduceBy part).construct ⊆
      Z.construct + (Zonotope.reduceByBox Z part).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  obtain ⟨β, hβ, hy₁eq⟩ := Zonotope.mem_nominalSet_iff.mp hy₁
  -- `Z`'s own coefficients: the kept half of `β`, the dropped half zeroed
  obtain ⟨α, hα⟩ : ∃ α : Fin Z.h → ℝ, ∀ j, α j =
      Sum.elim (fun l : Fin q => β (Fin.castAdd n l)) (fun _ : Fin r => (0:ℝ))
        (Pair.equivSum (Fin q) (Fin r) (part.index.symm j)) := ⟨_, fun _ => rfl⟩
  have hleft : ∀ l : Fin q, α (part.left l) = β (Fin.castAdd n l) := by
    intro l
    simp only [hα, Partition.left, Partition.on, Equiv.symm_apply_apply]
    rfl
  have hright : ∀ l : Fin r, α (part.right l) = 0 := by
    intro l
    simp only [hα, Partition.right, Partition.on, Equiv.symm_apply_apply]
    rfl
  have hαbound : ∀ j, |α j| ≤ 1 := by
    intro j
    obtain ⟨s, hs⟩ : ∃ s, Pair.equivSum (Fin q) (Fin r) (part.index.symm j) = s := ⟨_, rfl⟩
    rw [hα, hs]
    cases s with
    | inl l => simpa using hβ (Fin.castAdd n l)
    | inr l => simp
  -- the dropped-generator diagonal picks out one coordinate and drops the rest
  have hdiagsum : ∀ i, ∑ x : Fin n, toReal (diagonalBlock
      (radius fun i l => Z.G (part.right l) i) x i) * β (Fin.natAdd q x)
      = toReal (radius (fun i l => Z.G (part.right l) i) i) * β (Fin.natAdd q i) := by
    intro i
    simp only [toReal_diagonalBlock]
    exact Real.Zonotope.sum_diagonal_mul' _ (fun x => β (Fin.natAdd q x)) i
  -- the box's own point: the dropped rows' rounded-up radius, at `β`'s natAdd half
  set z : Vec ℝ n :=
    fun i => toReal (radius (fun i l => Z.G (part.right l) i) i) * β (Fin.natAdd q i) with hzdef
  have hzero : (0 : Vec ℝ n) ∈ (Zonotope.reduceByBox Z part).I_error.construct := fun i =>
    ⟨by show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i
        rw [toReal_zero]; exact le_refl 0,
     by show (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
        rw [toReal_zero]; exact le_refl 0⟩
  have hznom : z ∈ nominalSet (Zonotope.reduceByBox Z part) :=
    Zonotope.mem_nominalSet_iff.mpr ⟨fun l => β (Fin.natAdd q l), fun l => hβ _, fun i => by
      show z i = toReal (zero : 𝕋) + ∑ x, toReal
          (diagonalBlock (radius fun i l => Z.G (part.right l) i) x i) * β (Fin.natAdd q x)
      rw [hzdef, toReal_zero, zero_add, hdiagsum]⟩
  have hzmem : z ∈ (Zonotope.reduceByBox Z part).construct := by
    rw [show z = z + (0 : Vec ℝ n) from (add_zero z).symm]
    exact Set.add_mem_add hznom hzero
  refine ⟨_, Set.add_mem_add
      (Zonotope.mem_nominalSet_iff.mpr ⟨α, hαbound, fun _ => rfl⟩) hy₂, _, hzmem, ?_⟩
  funext i
  -- `y₁`'s own generator sum, split into the kept half and the dropped diagonal
  have hsum := Zonotope.aux_sum_univ_reduceBy_box (Z := Z) (part := part)
    (fun j => toReal (Fin.append (fun l => Z.G (part.left l))
      (diagonalBlock (radius fun i l => Z.G (part.right l) i)) j i) * β j)
  simp only [Fin.append_left, Fin.append_right] at hsum
  rw [hdiagsum i] at hsum
  have hy₁i : y₁ i = toReal (Z.c i)
      + (∑ l, toReal (Z.G (part.left l) i) * β (Fin.castAdd n l)
        + toReal (radius (fun i l => Z.G (part.right l) i) i) * β (Fin.natAdd q i)) :=
    (hy₁eq i).trans (congrArg (toReal (Z.c i) + ·) hsum)
  simp only [Pi.add_apply]
  rw [hy₁i, part.sum_split₂ fun j => toReal (Z.G j i) * α j]
  simp only [hleft, hright, mul_zero, Finset.sum_const_zero, add_zero]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
