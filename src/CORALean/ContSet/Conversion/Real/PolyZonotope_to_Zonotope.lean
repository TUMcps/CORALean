module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Function.CompTypeclasses

@[expose] public section

/-!
# A polynomial zonotope as a zonotope

Two enclosures, the cheaper first. `zonotope` reads every dependent generator as
an independent one — [1, Prop. 2.6] — since a monomial in factors of `[-1,1]`
is itself in `[-1,1]`. What is lost is the *sharing*, which is the whole
representation: the dependent generators are freed to move independently, so
every non-convexity goes and so does the exactness of a quadratic map.

`zonotopeEven` is [2, Prop. 1], restated as [3, Prop. 5], and is CORA's own
`zonotope(polyZonotope)`: an all-even column has its monomial in `[0,1]` rather
than `[-1,1]`, so half of that generator moves into the centre and only the other
half is left free. A column of zeros is the paper's `N`, whose monomial is `1`
exactly; CORA reads it as merely even and pays half a generator for it. Neither
keeps anything of the exponent matrix but the generators it indexed.

That freeing is why `zonotope_not_mono` holds: the result is a function of the
representation, not of the set, so [4]'s property (6) — which [4, Lemma 3] assumes
of it — is false here, two equal sets having enclosures that differ.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
* [2] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
* [3] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [4] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.zonotope (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at the generator count this conversion produces, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_zonotope {pZ : PolyZonotope α} (f : Fin (pZ.h + pZ.q) → α) :
    ∑ l : Fin pZ.zonotope.h, f l
      = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) :=
  Fin.sum_univ_add f

theorem PolyZonotope.zonotope_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonotope.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (PolyZonotope.monomial pZ.E a) b, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.abs_monomial_le_one pZ.E ha i
    · intro j
      simpa using hb j
  · rw [PolyZonotope.aux_sum_univ_zonotope]
    simp only [PolyZonotope.zonotope, Fin.append_left, Fin.append_right]
    abel

/-- How much of a dependent generator is left free: none of a constant column,
half of an all-even one, all of the rest. -/
noncomputable def PolyZonotope.aux_evenWeight {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : ℝ :=
  if ∀ k, E k i = 0 then 0 else if ∀ k, E k i % 2 = 0 then 1 / 2 else 1

/-- The coefficient that free generator is given, so that what the centre already
holds plus this much of the generator is the monomial. -/
noncomputable def PolyZonotope.aux_evenCoeff {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin p → ℝ) (i : Fin h) : ℝ :=
  if ∀ k, E k i = 0 then 0
  else if ∀ k, E k i % 2 = 0 then 2 * PolyZonotope.monomial E a i - 1
  else PolyZonotope.monomial E a i

/-- A column of zeros reads every factor at exponent zero, so its monomial is
`1` whatever the factors are. -/
theorem PolyZonotope.aux_monomial_eq_one {p h : ℕ} {E : Fin p → Fin h → ℕ} {i : Fin h}
    (hE : ∀ k, E k i = 0) (a : Fin p → ℝ) : PolyZonotope.monomial E a i = 1 :=
  Finset.prod_eq_one fun k _ => by rw [hE k, pow_zero]

/-- An all-even column's monomial is a product of even powers, so it never goes
below zero — which is what lets its generator be halved. -/
theorem PolyZonotope.aux_monomial_nonneg {p h : ℕ} {E : Fin p → Fin h → ℕ} {i : Fin h}
    (hE : ∀ k, E k i % 2 = 0) (a : Fin p → ℝ) : 0 ≤ PolyZonotope.monomial E a i :=
  Finset.prod_nonneg fun k _ => Even.pow_nonneg (Nat.even_iff.mpr (hE k)) (a k)

/-- What the centre keeps plus what the free generator reaches is the monomial,
in each of the three cases. -/
theorem PolyZonotope.aux_evenWeight_smul {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    (1 - PolyZonotope.aux_evenWeight E i)
        + PolyZonotope.aux_evenCoeff E a i * PolyZonotope.aux_evenWeight E i
      = PolyZonotope.monomial E a i := by -- --- PROOF ---
  rw [PolyZonotope.aux_evenWeight, PolyZonotope.aux_evenCoeff]
  split_ifs with hz he
  · -- a constant column: the centre takes all of it
    rw [PolyZonotope.aux_monomial_eq_one hz a]
    ring
  · -- an all-even column: half in the centre, half left free
    ring
  · -- anything else: the centre takes none of it
    ring

/-- Every coefficient a free generator is given is admissible, an all-even
column because its monomial lies in `[0,1]`. -/
theorem PolyZonotope.aux_abs_evenCoeff_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) :
    |PolyZonotope.aux_evenCoeff E a i| ≤ 1 := by -- --- PROOF ---
  rw [PolyZonotope.aux_evenCoeff]
  split_ifs with hz he
  · rw [abs_zero]
    exact zero_le_one
  · -- `[0,1]` on the nose, so `2m - 1` stays inside `[-1,1]`
    have h₀ : 0 ≤ PolyZonotope.monomial E a i := PolyZonotope.aux_monomial_nonneg he a
    have h₁ : PolyZonotope.monomial E a i ≤ 1 :=
      le_trans (le_abs_self _) (PolyZonotope.abs_monomial_le_one E ha i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact PolyZonotope.abs_monomial_le_one E ha i

/-- The paper's `N`, `H` and `K` read off column by column rather than as three
index sets: a zero weight is a generator the paper drops. -/
noncomputable def PolyZonotope.zonotopeEven (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c + ∑ i, (1 - PolyZonotope.aux_evenWeight pZ.E i) • pZ.G i
  G := Fin.append (fun i => PolyZonotope.aux_evenWeight pZ.E i • pZ.G i) pZ.GI

/-- `Fin.sum_univ_add` at the generator count the tighter conversion produces,
the binder ascribed so that it matches the goal. -/
theorem PolyZonotope.aux_sum_univ_zonotopeEven {pZ : PolyZonotope α}
    (f : Fin (pZ.h + pZ.q) → α) :
    ∑ l : Fin pZ.zonotopeEven.h, f l
      = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotopeEven_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonotopeEven.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (fun i => PolyZonotope.aux_evenCoeff pZ.E a i) b, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.aux_abs_evenCoeff_le_one pZ.E ha i
    · intro j
      simpa using hb j
  · -- the centre's share and the free generator's share add back to the monomial
    have hsum : ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        = ∑ i, (1 - PolyZonotope.aux_evenWeight pZ.E i) • pZ.G i
          + ∑ i, PolyZonotope.aux_evenCoeff pZ.E a i
              • (PolyZonotope.aux_evenWeight pZ.E i • pZ.G i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, PolyZonotope.aux_evenWeight_smul]
    rw [PolyZonotope.aux_sum_univ_zonotopeEven]
    simp only [PolyZonotope.zonotopeEven, Fin.append_left, Fin.append_right]
    rw [hsum]
    abel

/-- The square of one factor: it denotes `[0,1]`, its generator reaching `[-1,1]`. -/
abbrev PolyZonotope.aux_sq : PolyZonotope (Vec ℝ 1) :=
  ⟨1, 1, 0, 0, fun _ _ => 1, fun _ _ => 2, Fin.elim0⟩

/-- A wider interval written affinely, whose generator is already tight. -/
abbrev PolyZonotope.aux_aff : PolyZonotope (Vec ℝ 1) :=
  ⟨1, 1, 0, fun _ => 1, fun _ _ => 1, fun _ _ => 1, Fin.elim0⟩

/-- [4]'s property (6) fails for `zonotope`: `α²` and `1 + α` denote `[0,1]` and
`[0,2]`, whose enclosures are `[-1,1]` and `[0,2]`. -/
theorem PolyZonotope.zonotope_not_mono :
    ¬ ∀ pZ₁ pZ₂ : PolyZonotope (Vec ℝ 1), pZ₁.construct ⊆ pZ₂.construct →
      pZ₁.zonotope.construct ⊆ pZ₂.zonotope.construct := by -- --- PROOF ---
  intro hmono
  -- the square's value is the affine one's, read at the factor `α² - 1`
  have hsub : PolyZonotope.aux_sq.construct ⊆ PolyZonotope.aux_aff.construct := by
    rintro _ ⟨a, β, ha, _, rfl⟩
    have hsq : a 0 ^ 2 ≤ 1 := by nlinarith [abs_le.1 (ha 0)]
    refine ⟨fun _ => a 0 ^ 2 - 1, Fin.elim0, fun k => ?_, fun j => j.elim0, ?_⟩
    · rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a 0)]
    · funext i
      simp [PolyZonotope.monomial]
  -- `-1` is in the square's enclosure, its generator being free there
  have hmem : (fun _ => -1 : Vec ℝ 1) ∈ PolyZonotope.aux_sq.zonotope.construct := by
    refine ⟨fun _ => -1, fun j => by norm_num, ?_⟩
    funext i
    simp [PolyZonotope.zonotope]
  -- and in none of the affine one's, whose coordinate never drops below zero
  obtain ⟨β, hβ, heq⟩ := hmono _ _ hsub hmem
  have h0 : (-1 : ℝ) = 1 + β ⟨0, by simp [PolyZonotope.zonotope]⟩ := by
    simpa [PolyZonotope.zonotope] using congrFun heq 0
  have hb := abs_le.1 (hβ ⟨0, by simp [PolyZonotope.zonotope]⟩)
  linarith [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
