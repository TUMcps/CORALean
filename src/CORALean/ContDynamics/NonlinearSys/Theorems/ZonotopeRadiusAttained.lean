import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul

/-!
# A zonotope attains its radius about a point

`|c - z✱| + Σ|G|` is `max |z - z✱|` over the set a zonotope denotes, coordinate by coordinate:
the point that attains it takes each generator with the sign that makes its contribution
agree with the centre's offset. This is what makes the radius `lagrangeRemainder` reads off a
zonotope a property of the set and not of its generators.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix

variable {d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate of a zonotope's point, written as its centre plus what the
generators contribute there. -/
theorem aux_attained_coord_eq (Z : Zonotope (Vec ℝ d)) (β : Fin Z.h → ℝ) (zs : Vec ℝ d)
    (j : Fin d) :
    (Z.c + ∑ k, β k • Z.G k) j - zs j = (Z.c j - zs j) + ∑ k, β k * Z.G k j := by
  rw [Pi.add_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- `γ` is `max |z - z✱|` over the set: some point of it attains the radius `|c - z✱| + Σ|G|`
in each coordinate. -/
theorem Real.Zonotope.radius_attained (Z₁ : Zonotope (Vec ℝ d)) (zs : Vec ℝ d) (j : Fin d) :
    ∃ z ∈ Z₁.construct, |Z₁.c j - zs j| + ∑ k, |Z₁.G k j| ≤ |z j - zs j| := by -- --- PROOF ---
  -- the sign that turns coordinate `j` of the centre offset into its absolute value
  set s : ℝ := if 0 ≤ Z₁.c j - zs j then 1 else -1 with hsdef
  have hs1 : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
  have hsabs : |s| = 1 := by rcases hs1 with h | h <;> simp [h]
  have hsc : s * (Z₁.c j - zs j) = |Z₁.c j - zs j| := by
    rw [hsdef]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  -- and the coefficients that turn every generator's contribution into its own
  set β : Fin Z₁.h → ℝ := fun k => if 0 ≤ s * Z₁.G k j then 1 else -1 with hβdef
  -- each coefficient is a sign
  have hb : ∀ k, |β k| ≤ 1 := by
    intro k
    simp only [hβdef]
    split_ifs <;> simp
  -- and each generator's contribution there is its own magnitude, signed like the centre's
  have hg : ∀ k, s * (β k * Z₁.G k j) = |Z₁.G k j| := by
    intro k
    have habs : |s * Z₁.G k j| = |Z₁.G k j| := by rw [abs_mul, hsabs, one_mul]
    simp only [hβdef]
    split_ifs with h
    · rw [← habs, abs_of_nonneg h]; ring
    · rw [← habs, abs_of_neg (lt_of_not_ge h)]; ring
  -- that point is in the zonotope, and its offset in coordinate `j` is the radius
  refine ⟨Z₁.c + ∑ k, β k • Z₁.G k, ⟨β, hb, rfl⟩, ?_⟩
  have hlhs : s * ((Z₁.c + ∑ k, β k • Z₁.G k) j - zs j)
      = |Z₁.c j - zs j| + ∑ k, |Z₁.G k j| := by
    rw [aux_attained_coord_eq, mul_add, hsc, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => hg k)
  calc |Z₁.c j - zs j| + ∑ k, |Z₁.G k j|
      = s * ((Z₁.c + ∑ k, β k • Z₁.G k) j - zs j) := hlhs.symm
    _ ≤ |(Z₁.c + ∑ k, β k • Z₁.G k) j - zs j| := by
        rcases hs1 with h | h
        · rw [h, one_mul]
          exact le_abs_self _
        · rw [h, neg_one_mul]
          exact neg_le_abs _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
