module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ConvHull
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

@[expose] public section

/-!
# `convHull` contains both operands

`PolyZonotope.convHull` is the chords of chords of the dependent parts, plus the generators of
`enclose(Z1, Z2)` for the independent blocks. A point of either operand is a point of its dependent
part plus a point of its independent zonotope. The first is a chord of the part with itself, which
`linComb_outer` puts in the inner `linComb`, and a chord of that set with anything of the other
side's, which puts it in the outer one (the parameter `1` for the first operand, `0` for the
second).
The second is a chord of the two zero-centered zonotopes, `Zonotope.linComb_outer`. The outer
`linComb` has no independent generators, so replacing them by the zonotope's loses nothing.

The statement is an enclosure of the *union*. It is not the convex hull of the union: the set the
result denotes holds only combinations of two points per operand, and `enclose(Z1, Z2)` is an
enclosure of the independent blocks, not their hull, so the result is neither contained in the hull
of the union nor does it contain it in general.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Where `R` has no independent generators, a point of `R` and a point of a zero-centered zonotope
add to a point of `R` with the zonotope's generators in its independent block. -/
theorem PolyZonotope.aux_replaceGI_mem (R : PolyZonotope α) (hq : R.q = 0) (Z : Zonotope α)
    (hc : Z.c = 0) {d z : α} (hd : d ∈ R.construct) (hz : z ∈ Z.construct) :
    d + z ∈ ({ R with q := Z.h, GI := Z.G } : PolyZonotope α).construct := by -- --- PROOF ---
  haveI : IsEmpty (Fin R.q) := by rw [hq]; infer_instance
  obtain ⟨a, -, ha, -, rfl⟩ := hd
  obtain ⟨β, hβ, rfl⟩ := hz
  refine ⟨a, β, ha, hβ, ?_⟩
  simp only [hc, zero_add, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-- A point of a dependent part is a chord of the part with itself. -/
theorem PolyZonotope.aux_point_mem_linComb (P : PolyZonotope α) {a : Fin P.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) : P.point a ∈ (P.linComb P).construct := by
  refine PolyZonotope.linComb_outer P P ⟨P.point a, P.point_mem_construct ha, P.point a,
    P.point_mem_construct ha, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩
  simp

/-- A zero-centered zonotope is in the chords with another one. -/
theorem PolyZonotope.aux_mem_linComb_left {Z₁ Z₂ : Zonotope α} (h₂ : (0 : α) ∈ Z₂.construct)
    {z : α} (hz : z ∈ Z₁.construct) : z ∈ (Z₁.linComb Z₂).construct :=
  Zonotope.linComb_outer Z₁ Z₂ ⟨z, hz, 0, h₂, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩

theorem PolyZonotope.aux_mem_linComb_right {Z₁ Z₂ : Zonotope α} (h₁ : (0 : α) ∈ Z₁.construct)
    {z : α} (hz : z ∈ Z₂.construct) : z ∈ (Z₁.linComb Z₂).construct :=
  Zonotope.linComb_outer Z₁ Z₂ ⟨0, h₁, z, hz, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.union_subset_convHull (pZ₁ pZ₂ : PolyZonotope α) :
    pZ₁.construct ∪ pZ₂.construct ⊆ (pZ₁.convHull pZ₂).construct := by -- --- PROOF ---
  -- the dependent parts, the independent zonotopes
  set A := pZ₁.noIndep with hA
  set B := pZ₂.noIndep with hB
  set Z₁ : Zonotope α := ⟨pZ₁.q, 0, pZ₁.GI⟩ with hZ₁
  set Z₂ : Zonotope α := ⟨pZ₂.q, 0, pZ₂.GI⟩ with hZ₂
  have h0 : (0 : α) ∈ Z₁.construct ∧ (0 : α) ∈ Z₂.construct :=
    ⟨⟨fun _ => 0, fun _ => by simp, by simp [hZ₁]⟩, ⟨fun _ => 0, fun _ => by simp, by simp [hZ₂]⟩⟩
  have hcZ : (Z₁.linComb Z₂).c = 0 := by simp [Zonotope.linComb, hZ₁, hZ₂]
  have hq : (((A.linComb A).linComb (B.linComb B)).q = 0) := rfl
  have hLA : A.point (fun _ => 0) ∈ (A.linComb A).construct :=
    PolyZonotope.aux_point_mem_linComb A (fun _ => by simp)
  have hLB : B.point (fun _ => 0) ∈ (B.linComb B).construct :=
    PolyZonotope.aux_point_mem_linComb B (fun _ => by simp)
  rintro x (⟨a, β, ha, hβ, rfl⟩ | ⟨a, β, ha, hβ, rfl⟩)
  · -- a point of the first operand: parameter `1` in both
    have hd : A.point a ∈ ((A.linComb A).linComb (B.linComb B)).construct :=
      PolyZonotope.linComb_outer _ _ ⟨A.point a, PolyZonotope.aux_point_mem_linComb A ha,
        B.point (fun _ => 0), hLB, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    have hz : (∑ j, β j • pZ₁.GI j) ∈ (Z₁.linComb Z₂).construct :=
      PolyZonotope.aux_mem_linComb_left h0.2 ⟨β, hβ, (zero_add _).symm⟩
    have := PolyZonotope.aux_replaceGI_mem _ hq _ hcZ hd hz
    exact this
  · -- a point of the second operand: parameter `0`
    have hd : B.point a ∈ ((A.linComb A).linComb (B.linComb B)).construct :=
      PolyZonotope.linComb_outer _ _ ⟨A.point (fun _ => 0), hLA, B.point a,
        PolyZonotope.aux_point_mem_linComb B ha, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    have hz : (∑ j, β j • pZ₂.GI j) ∈ (Z₁.linComb Z₂).construct :=
      PolyZonotope.aux_mem_linComb_right h0.1 ⟨β, hβ, (zero_add _).symm⟩
    have := PolyZonotope.aux_replaceGI_mem _ hq _ hcZ hd hz
    exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
