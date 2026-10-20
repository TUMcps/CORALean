module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHull
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombExactOfDependent
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# The convex hull, exactly — under the hypothesis [1, Prop. 9] leaves out

`Prop. 9` as printed is false when exactly one operand is empty: its step (28) replaces the union
by the linear combination inside the hull, and the left inclusion needs a point of the *other*
operand to pair with. The closed form carries the combination's constraint system `n + 1` times,
so it is empty whenever either operand is, while the hull is not: in one dimension, the hull of
`{0}` and `∅` is `{0}` and the formula gives `∅`.

Both operands non-empty is therefore carried. `qI = 0` is [1, Def. 5]'s representation, as for
`linComb`.

## Inputs
* `n` – ambient dimension
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* `hq₁` – first has no independent generators
* `hq₂` – second has no independent generators
* `hne₁` – first set is nonempty
* `hne₂` – second set is nonempty

## Conclusion
* the convex hull of the union is the result's set

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The convex hull of two non-empty operands, exactly. -/
theorem ConPolyZono.convHull_exact_of_nonempty {n : ℕ} (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0)
    (hne₁ : cPZ₁.construct.Nonempty) (hne₂ : cPZ₂.construct.Nonempty) : -- --- CONCL ---
    convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct)
      = (cPZ₁.convHull cPZ₂).construct := by -- --- PROOF ---
  have hq : (cPZ₁.linComb cPZ₂).qI = 0 := by simp [ConPolyZono.linComb, hq₁, hq₂]
  have hrk : Module.finrank ℝ (Vec ℝ n) + 1 ≤ n + 1 := by rw [Module.finrank_fin_fun ℝ]
  rw [ConPolyZono.convHull, ConPolyZono.convHullSingle_exact _ _ hq hrk,
    ← ConPolyZono.linComb_exact_of_dependent cPZ₁ cPZ₂ hq₁ hq₂]
  obtain ⟨y₁, hy₁⟩ := hne₁
  obtain ⟨y₂, hy₂⟩ := hne₂
  refine le_antisymm (convexHull_mono ?_)
    (convexHull_min ?_ (convex_convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct)))
  · -- the union sits inside the combination, and only here is a point needed
    rintro x (hx | hx)
    · exact ⟨x, hx, y₂, hy₂, 1, ⟨zero_le_one, le_refl 1⟩, by simp⟩
    · exact ⟨y₁, hy₁, x, hx, 0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
  · -- and the combination inside the hull, every segment being a convex one
    rintro x ⟨z₁, hz₁, z₂, hz₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    exact (convex_convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct))
      (subset_convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct) (Or.inl hz₁))
      (subset_convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct) (Or.inr hz₂))
      (a := lam) (b := 1 - lam) hl₀ (by linarith) (by ring)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
