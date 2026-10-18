module

public import CORALean.ContSet.Zonotope.Real.Operations.Aligned
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedExact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono

@[expose] public section

/-!
# Two aligned differences bound `Z ⊖ S` from both sides

[1, Prop. 4]: `Z ⊖ Z̄(Z, EW) ⊆ Z ⊖ EW ⊆ Z ⊖ Z̲(Z, EW)`, both outer terms computed by
generator-wise subtraction. Here `S` is any set with an aligned zonotope around it
and one inside it, which is what [1, Prop. 1] and [1, Prop. 2] supply for `S = EW`;
the subtraction is `minkDiffAligned`, exact by [1, Prop. 3] for scalings in `[0, 1]`.

As printed the right inclusion inherits [1, Prop. 2]'s use of `W`'s halfspaces and
fails with them (`aligned_subset_of_maxIn_counterexample`); with an inner zonotope
of `EW` it holds.

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

/-- [1, Prop. 4]: the generator-wise differences by an aligned zonotope around `S` and
one inside `S` are an inner and an outer approximation of `Z ⊖ S`. -/
theorem Zonotope.minkDiffAligned_bounds (Z : Zonotope α) (S : Set α) (co ci : α)
    (ao ai : Fin Z.h → ℝ) (hao : ∀ i, 0 ≤ ao i ∧ ao i ≤ 1) (hai : ∀ i, 0 ≤ ai i ∧ ai i ≤ 1)
    (hout : S ⊆ (Z.aligned co ao).construct)
    (hin : (Z.aligned ci ai).construct ⊆ S) : -- --- STMT ---
    (Z.minkDiffAligned (Z.aligned co ao) rfl).construct ⊆ minkowskiDiff Z.construct S ∧
      minkowskiDiff Z.construct S
        ⊆ (Z.minkDiffAligned (Z.aligned ci ai) rfl).construct := by -- --- PROOF ---
  rw [Z.minkDiffAligned_exact (Z.aligned co ao) rfl ao (fun i => (hao i).1)
      (fun i => (hao i).2) (fun _ => rfl),
    Z.minkDiffAligned_exact (Z.aligned ci ai) rfl ai (fun i => (hai i).1)
      (fun i => (hai i).2) (fun _ => rfl)]
  -- a larger subtrahend gives a smaller difference
  exact ⟨minkowskiDiff_mono subset_rfl hout, minkowskiDiff_mono subset_rfl hin⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
