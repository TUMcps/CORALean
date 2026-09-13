import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHull
import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombExactOfDependent

/-!
# The convex hull, exactly — under the hypothesis [1, Prop. 9] leaves out

`Prop. 9` as printed is false when exactly one operand is empty. Its step (28)
replaces the union by the linear combination inside the hull, and the left
inclusion there needs a point of the *other* operand to pair with; nothing says
one exists. The closed form carries the combination's constraint system `n + 1`
times, so it is empty whenever either operand is, while the hull it claims to be
is not: in one dimension, the hull of `{0}` and `∅` is `{0}` and the formula
gives `∅`. CORA does not inherit this — `@conPolyZono/convHull_` tests
`representsa_(cPZ,'emptySet',...)` first and returns the other set.

Both operands non-empty is therefore carried, and is what step (28) actually
needs. `q = 0` is [1, Def. 5]'s representation, as for `linComb`, which this
routes through; no condition on the exponent matrices enters, the fresh weight
factor on every replicated column making a degree-`0` one behave like any other.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The convex hull of two non-empty operands, exactly. -/
theorem ConPolyZono.convHull_exact_of_nonempty {n : ℕ} (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (hq₁ : cPZ₁.q = 0) (hq₂ : cPZ₂.q = 0)
    (hne₁ : cPZ₁.construct.Nonempty) (hne₂ : cPZ₂.construct.Nonempty) :
    convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct)
      = (cPZ₁.convHull cPZ₂).construct := by -- --- PROOF ---
  have hq : (cPZ₁.linComb cPZ₂).q = 0 := by simp [ConPolyZono.linComb, hq₁, hq₂]
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
