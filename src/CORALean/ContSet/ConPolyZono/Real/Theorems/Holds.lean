import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# What the constraint `A μ(α) ∈ b` satisfies

Three facts about `ConPolyZono.holds`, which `construct` is stated through and
which therefore stays beside the structure. Each is one or two lines, each is
about that definition alone, and they share a file rather than each taking one.

The point case recovers [1]'s equality; monotonicity is what makes a rounded
bound sound, so the float layer pays into `b` through it; and the congruence
says the constraint reads its data only through the vector `A μ(α)`, which is
what lets `compact` rewrite the constraint block.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

/-- The paper's equality, as the degenerate interval. -/
theorem ConPolyZono.holds_point_iff {p m s : ℕ} (A : Mat ℝ m s) (b : Vec ℝ m)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) :
    ConPolyZono.holds A (Interval.point b) EC a
      ↔ ∀ i, (A *ᵥ PolyZonotope.monomial EC a) i = b i :=
  forall_congr' fun _ => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- Widening a bound only admits more factor vectors, which is what makes a
rounded constraint sound. -/
theorem ConPolyZono.holds_mono {p m s : ℕ} {A : Mat ℝ m s} {b b' : Interval (Vec ℝ m)}
    {EC : Fin p → Fin s → ℕ} {a : Fin p → ℝ} (hinf : ∀ i, b'.inf i ≤ b.inf i)
    (hsup : ∀ i, b.sup i ≤ b'.sup i) (h : ConPolyZono.holds A b EC a) :
    ConPolyZono.holds A b' EC a :=
  fun i => ⟨le_trans (hinf i) (h i).1, le_trans (h i).2 (hsup i)⟩

/-- A rewriting of the constraint block that leaves `A μ(α)` alone leaves the
constraint alone — which is what compacting `A` and `EC` does. -/
theorem ConPolyZono.holds_congr {p p' m s s' : ℕ} {A : Mat ℝ m s} {A' : Mat ℝ m s'}
    {b : Interval (Vec ℝ m)} {EC : Fin p → Fin s → ℕ} {EC' : Fin p' → Fin s' → ℕ}
    {a : Fin p → ℝ} {a' : Fin p' → ℝ}
    (h : A' *ᵥ PolyZonotope.monomial EC' a' = A *ᵥ PolyZonotope.monomial EC a) :
    ConPolyZono.holds A b EC a ↔ ConPolyZono.holds A' b EC' a' := by
  rw [ConPolyZono.holds, ConPolyZono.holds, h]

end CORALean.Real
