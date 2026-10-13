import CORALean.ContSet.Equality.Float.API
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Global.Float.Instances.Dyadic.API

/-!
# Equality of float sets, certified

At `Dyadic 53`. `ContSet.eqBool` runs the class's conservative `isequal`, which for a float
representation is a certified structural test: entry by entry, `le` in both directions. Two
zonotopes written with different mantissas and exponents for the same numbers (`2 · 2⁰` against
`1 · 2¹`) are certified equal; a zonotope and its permutation (swapped generators, the same set)
are not: the test compares generators in order and is not CORA's merge of parallel ones, so that
`false` decides nothing. Boxes are tested the same way, by containment each way.

The theorem instances apply `ContSet.eqBool_sound` to the certified pair, getting the equality of
the denoted sets of reals, and `ContSet.neBool_of_construct_ne` to two boxes whose sets differ
(the point `3/2` is in one and not the other), getting `neBool = true`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.IsequalFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A zonotope with generators `(2, 0)`, `(0, 1)` and the same one with `2` written `1 · 2¹`. -/
def Z₁ : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def Z₂ : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 1, d 0 0], ![d 0 0, d 1 0]], box0⟩

/-- The same generators in the other order: the same set, but not certified equal. -/
def Z₃ : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 0 0, d 1 0], ![d 2 0, d 0 0]], box0⟩

#eval ContSet.eqBool Z₁ Z₂   -- true
#eval ContSet.eqBool Z₁ Z₃   -- false: a refutation of nothing
#eval ContSet.neBool Z₁ Z₂   -- false

/-- Two boxes in one dimension: `[0, 1]` and `[0, 2]`. -/
def I₁ : Interval (Vec D 1) := ⟨![d 0 0], ![d 1 0]⟩
def I₂ : Interval (Vec D 1) := ⟨![d 0 0], ![d 1 1]⟩

#eval ContSet.eqBool I₁ I₁   -- true
#eval ContSet.eqBool I₁ I₂   -- false
#eval ContSet.neBool I₁ I₂   -- true

set_option maxRecDepth 4096 in
/-- A certified `true` is a proof that the denoted sets of reals are equal. -/
theorem Z₁_eq_Z₂ : Z₁.construct = Z₂.construct :=
  ContSet.eqBool_sound (S := Zonotope (Vec D 2)) (s := Z₁) (t := Z₂) rfl

/-- `[0, 1] ≠ [0, 2]` as sets of reals, so `neBool` is `true` (as the run shows). -/
theorem I₁_ne_I₂ : ContSet.neBool I₁ I₂ = true := by -- --- PROOF ---
  -- the point `3/2` is in the second box and not in the first
  refine ContSet.neBool_of_construct_ne (S := Interval (Vec D 1)) fun h => ?_
  have h2 : (![3 / 2] : Vec ℝ 1) ∈ ContSet.construct I₂ := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    show toReal (d 0 0) ≤ (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) ≤ toReal (d 1 1)
    rw [toReal_d, toReal_d]
    norm_num
  have h1 := h ▸ h2
  have := (h1 0).2
  change (3 / 2 : ℝ) ≤ toReal (d 1 0) at this
  rw [toReal_d] at this
  norm_num at this

end CORALean.Examples.IsequalFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
