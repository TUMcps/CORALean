module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.Brouwer

@[expose] public section

/-!
# The fixed-point inclusion, for a convex error set

[1, Lemma 1]'s `A ⊖ B ⊆ S - 2c`, `S = {a + φ(a) | a ∈ A}`, with the convexity moved from `A`
to `B`: `A` is any set, `B` is nonempty, convex, compact and symmetric around `c`, and
`φ : A → B` is continuous. For `x ∈ A ⊖ B` the set `x + B` lies in `A`, and
`a ↦ x + 2c - φ(a)` maps it into itself, so Brouwer's theorem on `x + B` gives `a` with
`x + 2c = a + φ(a)`.

This is the form [1, Prop. 1] needs: there `A = R_aff(Δt)` is the affine image of an initial
set `X₀` that is only compact and nonempty, while the error set `B` is a zonotope.

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

/-- `A ⊖ B ⊆ S - 2c` for any `A`, `B` nonempty, convex, compact and symmetric around `c`, and
`φ : A → B` continuous, `S = {a + φ(a) | a ∈ A}`. -/
theorem minkowskiDiff_subset_of_continuous_of_convex {A B : Set V} (hB : IsCompact B)
    (hBc : Convex ℝ B) (hBne : B.Nonempty) {c : V} (hBs : ∀ b ∈ B, (2 : ℝ) • c - b ∈ B)
    {φ : V → V} (hφ : ContinuousOn φ A) (hφB : Set.MapsTo φ A B) :
    minkowskiDiff A B ⊆
      (fun s => s - (2 : ℝ) • c) '' {x | ∃ a ∈ A, x = a + φ a} := by -- --- PROOF ---
  intro x hx
  -- `x + B` lies in `A`, and `a ↦ x + (2c - φ(a))` maps it into itself
  set K := (fun b => x + b) '' B
  have hKA : K ⊆ A := by
    rintro _ ⟨b, hb, rfl⟩; exact hx b hb
  have hT : Set.MapsTo (fun a => x + ((2 : ℝ) • c - φ a)) K K := fun a ha =>
    ⟨_, hBs _ (hφB (hKA ha)), rfl⟩
  have hK : IsCompact K := hB.image (continuous_const.add continuous_id)
  have hKc : Convex ℝ K := by
    simpa [K, Set.image_add_left] using hBc.translate x
  obtain ⟨a, ha, hfix⟩ := exists_fixedPoint_of_isCompact_convex hK hKc (hBne.image _)
    (f := fun a => x + ((2 : ℝ) • c - φ a))
    (continuousOn_const.add (continuousOn_const.sub (hφ.mono hKA))) hT
  -- its fixed point `a` has `a + φ(a) = x + 2c`
  refine ⟨a + φ a, ⟨a, hKA ha, rfl⟩, ?_⟩
  nth_rewrite 1 [← hfix]
  abel_nf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
