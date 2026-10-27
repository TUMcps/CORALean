module

public import CORALean.ContSet.Zonotope.Real.Definitions.Aligned

@[expose] public section

/-!
# The pairing `minkDiffAligned` runs on is [1, Def. 3]'s alignment

`minkDiffAligned_exact` asks for `μ` pairing the two generator families index for index, which is
[1, Prop. 5]'s "without loss of generality, we re-order the generators". That is a *choice* of
witness for [1, Def. 3], and this is the record that it is one: the re-ordered hypothesis implies
the printed relation. Not an `iff`: the converse would have to produce the re-ordering, and
`IsAlignedWith` allows two generators of `Z₂` to pick the same generator of `Z₁`, which no injection
into `Fin Z₁.h` recovers — the paper rules that out with `HasNoAlignedGens` on `Z₂`, a hypothesis
this direction does not need.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `μ` – generator scalings

## Hypotheses
* `hh` – equal generator counts
* `hG` – generators of `Z₂` scale those of `Z₁`

## Conclusion
* `Z₁` is aligned with `Z₂`

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3]: an index-for-index scaling of `Z₁`'s generators onto `Z₂`'s is
an alignment witness. -/
theorem Zonotope.isAlignedWith_of_smul (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h)
    (μ : Fin Z₁.h → ℝ) (hG : ∀ i, Z₂.G (Fin.cast hh i) = μ i • Z₁.G i) :
    Z₁.IsAlignedWith Z₂ := by
  intro i
  exact ⟨Fin.cast hh.symm i, μ (Fin.cast hh.symm i), by simpa using (hG (Fin.cast hh.symm i)).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
