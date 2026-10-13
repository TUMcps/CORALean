module

public import CORALean.ContSet.Zonotope.Real.Definitions.Aligned

@[expose] public section

/-!
# The pairing `minkDiffAligned` runs on is [1, Def. 3]'s alignment

`minkDiffAligned_exact` asks for `μ` pairing the two generator families index
for index, which is [1, Prop. 5]'s "without loss of generality, we re-order the
generators". That is a *choice* of witness for [1, Def. 3], and this is the
record that it is one: the re-ordered hypothesis implies the printed relation,
so the closed form is applied exactly where the definition says it may be.

Not an `iff`. The converse would have to produce the re-ordering, and
`AlignedWith` allows two generators of `Z₂` to pick the same generator of `Z₁`,
which no injection into `Fin Z₁.h` recovers — the paper rules that out with
`NoAlignedGens` on `Z₂`, which is a hypothesis this direction does not need.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
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
theorem Zonotope.alignedWith_of_smul (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h)
    (μ : Fin Z₁.h → ℝ) (hG : ∀ i, Z₂.G (Fin.cast hh i) = μ i • Z₁.G i) :
    Z₁.AlignedWith Z₂ := by
  intro i
  exact ⟨Fin.cast hh.symm i, μ (Fin.cast hh.symm i), by simpa using (hG (Fin.cast hh.symm i)).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
