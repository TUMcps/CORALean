module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBox
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# Reduction reaches no further than the original plus its own box

The converse direction to `reduceBy_outer`, and the one an inner approximation
needs: `Ẑ ⊆ Z + E` with `E` the box `reduceByBox` names, so `E` is the error
bound the reduction pays rather than an estimate of it.

The witness is the point of the proof: a point of `Ẑ` keeps the coefficients of
the generators the partition kept and sets the dropped ones to `0`, which is a
point of `Z` because a zonotope's coefficients range over all of `[-1, 1]`. What
is left is the diagonal block, which is the box exactly.

`α` is that coefficient vector, read back onto `Z`'s own generator indices
through the partition's equivalence; `hleft` and `hright` are the two halves of
its definition and are what `sum_split₂` then needs.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what a partition drops also bounds the reduction from above: the
reduced zonotope lies inside the original plus the box it introduced. -/
theorem Zonotope.reduceBy_subset_add_box (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.reduceBy part).construct ⊆
      Z.construct + (Z.reduceByBox part).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxi⟩ := Zonotope.mem_construct_iff.mp hx
  -- the kept coefficients, read back onto `Z`'s own generator indices
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
  -- admissible either way: a kept coefficient, or the `0` a dropped one becomes
  have hαbound : ∀ j, |α j| ≤ 1 := by
    intro j
    obtain ⟨s, hs⟩ : ∃ s, Pair.equivSum (Fin q) (Fin r) (part.index.symm j) = s := ⟨_, rfl⟩
    rw [hα, hs]
    cases s with
    | inl l => simpa using hβ (Fin.castAdd n l)
    | inr l => simp
  -- the two summands: `Z` with the dropped coefficients zeroed, and the box
  refine Set.mem_add.mpr ⟨fun i => Z.c i + ∑ j, Z.G j i * α j,
    Zonotope.mem_construct_iff.mpr ⟨α, hαbound, fun i => rfl⟩,
    fun i => ∑ l : Fin n,
      Matrix.diagonal (fun i' => ∑ l', |Z.G (part.right l') i'|) l i * β (Fin.natAdd q l),
    Zonotope.mem_construct_iff.mpr
      ⟨fun l => β (Fin.natAdd q l), fun l => hβ _, fun i => by
        simp only [Zonotope.reduceByBox, Pi.zero_apply, zero_add]; rfl⟩, ?_⟩
  funext i
  rw [Pi.add_apply, hxi i, part.sum_split₂ fun j => Z.G j i * α j,
    Zonotope.sum_univ_reduceBy]
  simp only [Zonotope.reduceBy, Fin.append_left, Fin.append_right,
    hleft, hright, mul_zero, Finset.sum_const_zero, add_zero, add_assoc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
