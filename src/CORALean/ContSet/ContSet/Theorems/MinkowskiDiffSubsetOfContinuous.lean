module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.Brouwer

@[expose] public section

/-!
# The fixed-point inclusion

[1, Lemma 1]: for `A ⊂ ℝⁿ` nonempty, convex and compact, `B` centrally symmetric around `c`,
`φ : A → B` continuous and `S = {a + φ(a) | a ∈ A}`, `A ⊖ B ⊆ S - 2c` (19). A point `x` of
`A ⊖ B` keeps `x + (2c - φ(a))` in `A`, because `2c - φ(a)` is in `B`, so `a ↦ x + 2c - φ(a)`
maps `A` into itself and Brouwer's theorem (`exists_fixedPoint_of_isCompact_convex`) gives a
fixed point `a`, which is `x + 2c = a + φ(a)`. Stated in any finite-dimensional real normed
space; "centrally symmetric around `c`" is `b ∈ B → 2c - b ∈ B`.

Continuity cannot be dropped ([1, Remark 1], `minkowskiDiff_not_subset_of_discontinuous`).
Convexity of `A` can be traded for convexity and compactness of `B`
(`minkowskiDiff_subset_of_continuous_of_convex`).

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `A ⊖ B ⊆ S - 2c` for `A` nonempty, convex and compact, `B` symmetric around
`c` and `φ : A → B` continuous, `S = {a + φ(a) | a ∈ A}`. -/
theorem minkowskiDiff_subset_of_continuous {A B : Set V} (hA : IsCompact A)
    (hAc : Convex ℝ A) (hAne : A.Nonempty) {c : V} (hB : ∀ b ∈ B, (2 : ℝ) • c - b ∈ B)
    {φ : V → V} (hφ : ContinuousOn φ A) (hφB : Set.MapsTo φ A B) : -- --- CONCL ---
    minkowskiDiff A B ⊆
      (fun s => s - (2 : ℝ) • c) '' {x | ∃ a ∈ A, x = a + φ a} := by -- --- PROOF ---
  intro x hx
  -- `a ↦ x + (2c - φ(a))` maps `A` into itself
  have hT : Set.MapsTo (fun a => x + ((2 : ℝ) • c - φ a)) A A := fun a ha =>
    hx _ (hB _ (hφB ha))
  obtain ⟨a, ha, hfix⟩ := exists_fixedPoint_of_isCompact_convex hA hAc hAne
    (f := fun a => x + ((2 : ℝ) • c - φ a))
    (continuousOn_const.add (continuousOn_const.sub hφ)) hT
  -- its fixed point `a` has `a + φ(a) = x + 2c`
  refine ⟨a + φ a, ⟨a, ha, rfl⟩, ?_⟩
  nth_rewrite 1 [← hfix]
  abel_nf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
