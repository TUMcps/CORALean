module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Union
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemUnionUpperIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.EvalUnionLower
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SumUnionE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialEqZeroOfNoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionDomainIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ExistsUnionFactorsLeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ExistsUnionFactorsRight
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import Mathlib.Tactic.Module
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLower
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# The union, exactly — under the hypothesis [1, Thm. 1] leaves out

`Thm. 1` as printed is false. Its Appendix A.3 argues that on the branch selecting `CPZ₁` every
column of `CPZ₂`'s blocks vanishes. An all-zero exponent column is a degree-`0` monomial, equals
`1` whatever the factors are, and so is added on *both* branches: `⟨0, G = 3, E = 1⟩ ∪ ⟨0, G = 5,
E = 0⟩` is `[-3,3] ∪ {5}`, but the formula also reaches `8`. CORA's `@conPolyZono/or` inherits the
same gap.

`HasNoZeroCol` on all four exponent matrices is what A.3 needs, weaker than `regular`. `qI = 0` is
`Def. 5`'s representation, as for `linComb_exact_of_dependent`.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* `hq₁` – first has no independent generators
* `hq₂` – second has no independent generators
* `hE₁` – first exponent matrix has no zero column
* `hR₁` – first constraint exponents have no zero column
* `hE₂` – second exponent matrix has no zero column
* `hR₂` – second constraint exponents have no zero column

## Conclusion
* the union is the result's set

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The union's lower rows of two systems of equations, read as equations. -/
theorem ConPolyZono.aux_holds_unionLower_iff {p₁ p₂ : ℕ} {P₁ : PolyLevelSet p₁}
    {P₂ : PolyLevelSet p₂} (h₁ : ∀ i, P₁.op i = .eq) (h₂ : ∀ i, P₂.op i = .eq)
    (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
    (∀ i, ((ConPolyZono.unionLower P₁ P₂).op i).holds ((ConPolyZono.unionLower P₁ P₂).eval a i))
      ↔ ∀ i, (ConPolyZono.unionLower P₁ P₂).eval a i = 0 := by -- --- PROOF ---
  refine forall_congr' fun i => ?_
  rw [show (ConPolyZono.unionLower P₁ P₂).op i = .eq from LevelSet.append_op_eq h₁ h₂ i]
  rfl

/-- A point of the closed form lies in one operand or the other: the branch
`union_domain_iff` hands back says which, and pins the other one's block to `0`. -/
theorem ConPolyZono.aux_mem_of_holds (cPZ₁ cPZ₂ : ConPolyZono α)
    (hE₁ : ConPolyZono.HasNoZeroCol cPZ₁.E) (hE₂ : ConPolyZono.HasNoZeroCol cPZ₂.E)
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (hab : ∀ k, |a k| ≤ 1)
    (hup : a ∈ (ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).construct)
    (hlow : ∀ i, ((ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).op i).holds
      ((ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).eval a i)) : -- --- CONCL ---
    (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
        + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
            • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
      ∈ cPZ₁.construct ∪ cPZ₂.construct := by -- --- PROOF ---
  replace hlow := (ConPolyZono.aux_holds_unionLower_iff cPZ₁.cons_eq cPZ₂.cons_eq a).mp hlow
  have hbr := (ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
    (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
    (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
    (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
    (hab _) (hab _) (fun k => hab _)).mp ((ConPolyZono.mem_unionUpper_iff a).mp hup).2
  simp only [Set.mem_union]
  rcases hbr with ⟨hx1, hy1, hv⟩ | ⟨hx1, hy1, hu⟩
  · -- the selector is `1`, so the second operand's block is pinned to zero
    left
    refine ⟨fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)), fun _ => 0, fun _ => by simp,
      (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ₁.cons_eq cPZ₁.cons_dom).mpr
        ⟨fun k => hab _, fun r => ?_⟩, ?_⟩
    · have h := hlow (Fin.castAdd cPZ₂.cons.m r)
      rw [ConPolyZono.eval_unionLower, Fin.append_left, hx1] at h
      linarith
    · have hG₂ : (∑ i, PolyZonotope.monomial cPZ₂.E
          (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) i • cPZ₂.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₂ hv i, zero_smul]
      rw [ConPolyZono.sum_unionE cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G cPZ₁.E cPZ₂.E a, hG₂, hx1,
        Finset.sum_eq_zero (fun j (_ : j ∈ Finset.univ) => zero_smul ℝ (cPZ₁.GI j))]
      module
  · -- and the mirror, the selector `-1` pinning the first operand's block
    right
    refine ⟨fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)), fun _ => 0, fun _ => by simp,
      (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ₂.cons_eq cPZ₂.cons_dom).mpr
        ⟨fun k => hab _, fun r => ?_⟩, ?_⟩
    · have h := hlow (Fin.natAdd cPZ₁.cons.m r)
      rw [ConPolyZono.eval_unionLower, Fin.append_right, hx1] at h
      linarith
    · have hG₁ : (∑ i, PolyZonotope.monomial cPZ₁.E
          (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) i • cPZ₁.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₁ hu i, zero_smul]
      rw [ConPolyZono.sum_unionE cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G cPZ₁.E cPZ₂.E a, hG₁, hx1,
        Finset.sum_eq_zero (fun j (_ : j ∈ Finset.univ) => zero_smul ℝ (cPZ₂.GI j))]
      module


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_exact_of_noZeroCol (cPZ₁ cPZ₂ : ConPolyZono α)
    (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0)
    (hE₁ : ConPolyZono.HasNoZeroCol cPZ₁.E) (hR₁ : ConPolyZono.HasNoZeroCol cPZ₁.cons.R)
    (hE₂ : ConPolyZono.HasNoZeroCol cPZ₂.E)
    (hR₂ : ConPolyZono.HasNoZeroCol cPZ₂.cons.R) : -- --- CONCL ---
    cPZ₁.construct ∪ cPZ₂.construct = (cPZ₁.union cPZ₂).construct := by -- --- PROOF ---
  ext x
  simp only [Set.mem_union]
  constructor
  · rintro (⟨a₁, β₁, hβ₁, hsat₁, rfl⟩ | ⟨a₂, β₂, hβ₂, hsat₂, rfl⟩)
    · -- a point of the first operand, at the branch that selects it
      have ha₁ := ((PolyLevelSet.mem_construct_iff_of_eq_unit cPZ₁.cons_eq cPZ₁.cons_dom).mp
        hsat₁).1
      obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
        ConPolyZono.exists_unionFactors_left (p₂ := cPZ₂.p) 1 (by norm_num) ha₁
      have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) k = 0 := hv
      refine ⟨a, fun _ => 0, fun j => j.elim0, ?_, ?_⟩
      -- the selector rows and the operands' rows, at the branch's factors
      · refine (PolyLevelSet.mem_andRows_iff _ _ a).mpr ⟨?_,
          (ConPolyZono.aux_holds_unionLower_iff cPZ₁.cons_eq cPZ₂.cons_eq a).mpr ?_⟩
        · exact (ConPolyZono.mem_unionUpper_iff a).mpr ⟨hab,
            (ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
              (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
              (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
              (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
              (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
              (fun k => hab _)).mpr (Or.inl ⟨hx1, hy1, hv⟩)⟩
        · refine Fin.addCases (fun r => ?_) fun r => ?_
          · rw [ConPolyZono.eval_unionLower, Fin.append_left]
            have h1 : (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) = a₁ := funext hu
            rw [h1, hx1]
            have h := ((PolyLevelSet.mem_construct_iff_of_eq cPZ₁.cons_eq).mp hsat₁).2 r
            linarith
          · -- the other operand's rows, its whole left side pinned to zero
            rw [ConPolyZono.eval_unionLower, Fin.append_right]
            have hzero : (cPZ₂.cons.A *ᵥ PolyZonotope.monomial cPZ₂.cons.R
                fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) r = 0 := by
              show (∑ l, cPZ₂.cons.A r l * PolyZonotope.monomial cPZ₂.cons.R _ l) = 0
              exact Finset.sum_eq_zero fun l _ => by
                rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hR₂ hz l, mul_zero]
            rw [hzero, hx1]
            ring
      · -- the point itself: at the selector `1` the center moves to `c₁`
        have hβ₀ : (∑ j, β₁ j • cPZ₁.GI j) = 0 :=
          Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
        have hG₂ : (∑ i, PolyZonotope.monomial cPZ₂.E
            (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) i • cPZ₂.G i) = 0 :=
          Finset.sum_eq_zero fun i _ => by
            rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₂ hz i, zero_smul]
        have h1 : (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) = a₁ := funext hu
        show cPZ₁.c + (∑ i, PolyZonotope.monomial cPZ₁.E a₁ i • cPZ₁.G i)
            + (∑ j, β₁ j • cPZ₁.GI j)
          = (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
            + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
                • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
        rw [ConPolyZono.sum_unionE, h1, hG₂, hβ₀, hx1]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        module
    · -- the mirror, a point of the second operand at the other branch
      have ha₂ := ((PolyLevelSet.mem_construct_iff_of_eq_unit cPZ₂.cons_eq cPZ₂.cons_dom).mp
        hsat₂).1
      obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
        ConPolyZono.exists_unionFactors_right (p₁ := cPZ₁.p) (-1) (by norm_num) ha₂
      have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) k = 0 := hu
      refine ⟨a, fun _ => 0, fun j => j.elim0, ?_, ?_⟩
      · refine (PolyLevelSet.mem_andRows_iff _ _ a).mpr ⟨?_,
          (ConPolyZono.aux_holds_unionLower_iff cPZ₁.cons_eq cPZ₂.cons_eq a).mpr ?_⟩
        · exact (ConPolyZono.mem_unionUpper_iff a).mpr ⟨hab,
            (ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
              (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
              (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
              (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
              (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
              (fun k => hab _)).mpr (Or.inr ⟨hx1, hy1, hu⟩)⟩
        · refine Fin.addCases (fun r => ?_) fun r => ?_
          · -- the first operand's rows, its whole left side pinned to zero
            rw [ConPolyZono.eval_unionLower, Fin.append_left]
            have hzero : (cPZ₁.cons.A *ᵥ PolyZonotope.monomial cPZ₁.cons.R
                fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) r = 0 := by
              show (∑ l, cPZ₁.cons.A r l * PolyZonotope.monomial cPZ₁.cons.R _ l) = 0
              exact Finset.sum_eq_zero fun l _ => by
                rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hR₁ hz l, mul_zero]
            rw [hzero, hx1]
            ring
          · rw [ConPolyZono.eval_unionLower, Fin.append_right]
            have h2 : (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) = a₂ := funext hv
            rw [h2, hx1]
            have h := ((PolyLevelSet.mem_construct_iff_of_eq cPZ₂.cons_eq).mp hsat₂).2 r
            linarith
      · -- and the point, the selector `-1` moving the center to `c₂`
        have hβ₀ : (∑ j, β₂ j • cPZ₂.GI j) = 0 :=
          Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
        have hG₁ : (∑ i, PolyZonotope.monomial cPZ₁.E
            (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) i • cPZ₁.G i) = 0 :=
          Finset.sum_eq_zero fun i _ => by
            rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₁ hz i, zero_smul]
        have h2 : (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) = a₂ := funext hv
        show cPZ₂.c + (∑ i, PolyZonotope.monomial cPZ₂.E a₂ i • cPZ₂.G i)
            + (∑ j, β₂ j • cPZ₂.GI j)
          = (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
            + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
                • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
        rw [ConPolyZono.sum_unionE, h2, hG₁, hβ₀, hx1]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        module
  -- back: the constraint splits, and the branch it leaves says which operand
  · rintro ⟨a, β, hβ, hsat, rfl⟩
    obtain ⟨hup, hlow⟩ := (PolyLevelSet.mem_andRows_iff _ _ a).mp hsat
    have hab := ((ConPolyZono.mem_unionUpper_iff a).mp hup).1
    have hq0 : (cPZ₁.union cPZ₂).qI = 0 := rfl
    have hz : (∑ j, β j • (cPZ₁.union cPZ₂).GI j) = 0 :=
      Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
    rw [hz, add_zero]
    exact ConPolyZono.aux_mem_of_holds cPZ₁ cPZ₂ hE₁ hE₂ a hab hup hlow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
