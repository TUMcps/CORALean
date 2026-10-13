import CORALean.ContSet.ConPolyZono.Real.Operations.Union
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsSharedIff
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsUnionUpperIff
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerRight
import CORALean.ContSet.ConPolyZono.Real.Operations.SumUnionE
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionDomainIff
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import Mathlib.Tactic.Module

/-!
# The union, exactly — under the hypothesis [1, Thm. 1] leaves out

`Thm. 1` as printed is false. Its Appendix A.3 argues that on the branch selecting
`CPZ₁` every column of `CPZ₂`'s blocks vanishes, `CPZ₂`'s own factors being pinned
to `0` there. An all-zero exponent column is a degree-`0` monomial, equals `1`
whatever the factors are, and so is added on *both* branches. `Def. 5` names that
case — `regular` forbids it — but `Thm. 1` states nothing about its inputs:
`⟨0, G = 3, E = 1⟩ ∪ ⟨0, G = 5, E = 0⟩` is `[-3,3] ∪ {5}`; the formula also reaches `8`.
CORA's `@conPolyZono/or` builds the same matrices and inherits the same gap.

`NoZeroCol` on all four exponent matrices is what A.3 actually needs, and is
weaker than `regular`: duplicate columns never enter the argument. It is also the
weakest hypothesis on the exponent matrices alone, since an all-zero column of
`E₂` is broken by putting all of `G₂` on it.

`q = 0` is `Def. 5`'s representation, as for `linComb_exact_of_dependent`; `b`
non-empty is what an interval bound costs where [1]'s is crisp — a crossed `b`
would make *both* branches unsatisfiable, not just its own.

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

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The factor vector of the branch that keeps the first operand: its own
factors, the second operand's pinned to `0`, and the two fresh ones at `t`. -/
theorem ConPolyZono.aux_factors_left {p₁ p₂ : ℕ} (t : ℝ) (ht : |t| ≤ 1)
    {a₁ : Fin p₁ → ℝ} (ha₁ : ∀ k, |a₁ k| ≤ 1) :
    ∃ a : Fin (p₁ + p₂ + 2) → ℝ, (∀ k, |a k| ≤ 1)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.castAdd p₂ k)) = a₁ k)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.natAdd p₁ k)) = 0)
      ∧ a (ConPolyZono.unionSel p₁ p₂) = t
      ∧ a (Fin.natAdd (p₁ + p₂) 1) = t := by -- --- PROOF ---
  refine ⟨Fin.append (Fin.append a₁ (fun _ => (0:ℝ))) ![t, t], ?_, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · rw [Fin.append_left]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; exact ha₁ j
      · rw [Fin.append_right]; simp
    · rw [Fin.append_right]
      fin_cases k <;> simpa using ht
  · exact fun k => by rw [Fin.append_left, Fin.append_left]
  · exact fun k => by rw [Fin.append_left, Fin.append_right]
  · rw [ConPolyZono.unionSel, Fin.append_right]; rfl
  · rw [Fin.append_right]; rfl

/-- The mirror, keeping the second operand instead. -/
theorem ConPolyZono.aux_factors_right {p₁ p₂ : ℕ} (t : ℝ) (ht : |t| ≤ 1)
    {a₂ : Fin p₂ → ℝ} (ha₂ : ∀ k, |a₂ k| ≤ 1) :
    ∃ a : Fin (p₁ + p₂ + 2) → ℝ, (∀ k, |a k| ≤ 1)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.castAdd p₂ k)) = 0)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.natAdd p₁ k)) = a₂ k)
      ∧ a (ConPolyZono.unionSel p₁ p₂) = t
      ∧ a (Fin.natAdd (p₁ + p₂) 1) = t := by -- --- PROOF ---
  refine ⟨Fin.append (Fin.append (fun _ => (0:ℝ)) a₂) ![t, t], ?_, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · rw [Fin.append_left]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; simp
      · rw [Fin.append_right]; exact ha₂ j
    · rw [Fin.append_right]
      fin_cases k <;> simpa using ht
  · exact fun k => by rw [Fin.append_left, Fin.append_left]
  · exact fun k => by rw [Fin.append_left, Fin.append_right]
  · rw [ConPolyZono.unionSel, Fin.append_right]; rfl
  · rw [Fin.append_right]; rfl

/-- A point of the closed form lies in one operand or the other: the branch
`union_domain_iff` hands back says which, and pins the other one's block to `0`. -/
theorem ConPolyZono.aux_mem_of_holds (cPZ₁ cPZ₂ : ConPolyZono α)
    (hE₁ : ConPolyZono.NoZeroCol cPZ₁.E) (hE₂ : ConPolyZono.NoZeroCol cPZ₂.E)
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (hab : ∀ k, |a k| ≤ 1)
    (hup : ConPolyZono.holds (ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
      ConPolyZono.unionUpperB (ConPolyZono.unionUpperEC cPZ₁.p cPZ₂.p) a)
    (hlow : ConPolyZono.holds (ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b)
      (ConPolyZono.unionLowerB cPZ₁.b cPZ₂.b)
      (ConPolyZono.unionLowerEC cPZ₁.EC cPZ₂.EC) a) :
    (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
        + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
            • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
      ∈ cPZ₁.construct ∪ cPZ₂.construct := by -- --- PROOF ---
  have hbr := (ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
    (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
    (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
    (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
    (hab _) (hab _) (fun k => hab _)).mp ((ConPolyZono.holds_unionUpper_iff a).mp hup)
  simp only [Set.mem_union]
  rcases hbr with ⟨hx1, hy1, hv⟩ | ⟨hx1, hy1, hu⟩
  · -- the selector is `1`, so the second operand's block is pinned to zero
    left
    refine ⟨fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)), fun _ => 0,
      fun k => hab _, fun _ => by simp, fun r => ?_, ?_⟩
    · have h := hlow (Fin.castAdd cPZ₂.m r)
      rw [ConPolyZono.mulVec_unionLower_left cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b cPZ₁.EC cPZ₂.EC
        a r, hx1] at h
      simp only [ConPolyZono.unionLowerB, Fin.append_left] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have hG₂ : (∑ i, PolyZonotope.monomial cPZ₂.E
          (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) i • cPZ₂.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₂ hv i, zero_smul]
      rw [ConPolyZono.sum_unionE cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G cPZ₁.E cPZ₂.E a, hG₂, hx1,
        Finset.sum_eq_zero (fun j (_ : j ∈ Finset.univ) => zero_smul ℝ (cPZ₁.GI j))]
      module
  · -- and the mirror, the selector `-1` pinning the first operand's block
    right
    refine ⟨fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)), fun _ => 0,
      fun k => hab _, fun _ => by simp, fun r => ?_, ?_⟩
    · have h := hlow (Fin.natAdd cPZ₁.m r)
      rw [ConPolyZono.mulVec_unionLower_right cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b cPZ₁.EC cPZ₂.EC
        a r, hx1] at h
      simp only [ConPolyZono.unionLowerB, Fin.append_right] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have hG₁ : (∑ i, PolyZonotope.monomial cPZ₁.E
          (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) i • cPZ₁.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₁ hu i, zero_smul]
      rw [ConPolyZono.sum_unionE cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G cPZ₁.E cPZ₂.E a, hG₁, hx1,
        Finset.sum_eq_zero (fun j (_ : j ∈ Finset.univ) => zero_smul ℝ (cPZ₂.GI j))]
      module


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_exact_of_noZeroCol (cPZ₁ cPZ₂ : ConPolyZono α)
    (hq₁ : cPZ₁.q = 0) (hq₂ : cPZ₂.q = 0)
    (hb₁ : cPZ₁.b.IsNonempty (ι := Fin cPZ₁.m))
    (hb₂ : cPZ₂.b.IsNonempty (ι := Fin cPZ₂.m))
    (hE₁ : ConPolyZono.NoZeroCol cPZ₁.E) (hEC₁ : ConPolyZono.NoZeroCol cPZ₁.EC)
    (hE₂ : ConPolyZono.NoZeroCol cPZ₂.E) (hEC₂ : ConPolyZono.NoZeroCol cPZ₂.EC) :
    cPZ₁.construct ∪ cPZ₂.construct = (cPZ₁.union cPZ₂).construct := by -- --- PROOF ---
  have hb₁' : ∀ i, cPZ₁.b.inf i ≤ cPZ₁.b.sup i := fun i => hb₁ i
  have hb₂' : ∀ i, cPZ₂.b.inf i ≤ cPZ₂.b.sup i := fun i => hb₂ i
  ext x
  simp only [Set.mem_union]
  constructor
  · rintro (⟨a₁, β₁, ha₁, hβ₁, hsat₁, rfl⟩ | ⟨a₂, β₂, ha₂, hβ₂, hsat₂, rfl⟩)
    · -- a point of the first operand, at the branch that selects it
      obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
        ConPolyZono.aux_factors_left (p₂ := cPZ₂.p) 1 (by norm_num) ha₁
      have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) k = 0 := hv
      refine ⟨a, fun _ => 0, hab, fun j => j.elim0, ?_, ?_⟩
      · refine (ConPolyZono.holds_shared_iff _ _ _ _ _ _ a).mpr ⟨?_, ?_⟩
        · exact (ConPolyZono.holds_unionUpper_iff a).mpr
            ((ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
              (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
              (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
              (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
              (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
              (fun k => hab _)).mpr (Or.inl ⟨hx1, hy1, hv⟩))
        · refine Fin.addCases (fun r => ?_) fun r => ?_
          · rw [ConPolyZono.mulVec_unionLower_left]
            have h1 : (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) = a₁ := funext hu
            rw [h1, hx1]
            have h := hsat₁ r
            simp only [ConPolyZono.unionLowerB, Fin.append_left]
            constructor <;> linarith [h.1, h.2]
          · -- the other operand's rows, its whole left side pinned to zero
            rw [ConPolyZono.mulVec_unionLower_right]
            have hzero : (cPZ₂.A *ᵥ PolyZonotope.monomial cPZ₂.EC
                fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) r = 0 := by
              show (∑ l, cPZ₂.A r l * PolyZonotope.monomial cPZ₂.EC _ l) = 0
              exact Finset.sum_eq_zero fun l _ => by
                rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hEC₂ hz l, mul_zero]
            rw [hzero, hx1]
            simp only [ConPolyZono.unionLowerB, Fin.append_right]
            constructor <;> linarith [hb₂' r]
      · -- the point itself: at the selector `1` the centre moves to `c₁`
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
      obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
        ConPolyZono.aux_factors_right (p₁ := cPZ₁.p) (-1) (by norm_num) ha₂
      have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) k = 0 := hu
      refine ⟨a, fun _ => 0, hab, fun j => j.elim0, ?_, ?_⟩
      · refine (ConPolyZono.holds_shared_iff _ _ _ _ _ _ a).mpr ⟨?_, ?_⟩
        · exact (ConPolyZono.holds_unionUpper_iff a).mpr
            ((ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
              (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
              (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
              (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
              (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
              (fun k => hab _)).mpr (Or.inr ⟨hx1, hy1, hu⟩))
        · refine Fin.addCases (fun r => ?_) fun r => ?_
          · -- the first operand's rows, its whole left side pinned to zero
            rw [ConPolyZono.mulVec_unionLower_left]
            have hzero : (cPZ₁.A *ᵥ PolyZonotope.monomial cPZ₁.EC
                fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) r = 0 := by
              show (∑ l, cPZ₁.A r l * PolyZonotope.monomial cPZ₁.EC _ l) = 0
              exact Finset.sum_eq_zero fun l _ => by
                rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hEC₁ hz l, mul_zero]
            rw [hzero, hx1]
            simp only [ConPolyZono.unionLowerB, Fin.append_left]
            constructor <;> linarith [hb₁' r]
          · rw [ConPolyZono.mulVec_unionLower_right]
            have h2 : (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) = a₂ := funext hv
            rw [h2, hx1]
            have h := hsat₂ r
            simp only [ConPolyZono.unionLowerB, Fin.append_right]
            constructor <;> linarith [h.1, h.2]
      · -- and the point, the selector `-1` moving the centre to `c₂`
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
  · rintro ⟨a, β, hab, hβ, hsat, rfl⟩
    obtain ⟨hup, hlow⟩ := (ConPolyZono.holds_shared_iff _ _ _ _ _ _ a).mp hsat
    have hq0 : (cPZ₁.union cPZ₂).q = 0 := rfl
    have hz : (∑ j, β j • (cPZ₁.union cPZ₂).GI j) = 0 :=
      Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
    rw [hz, add_zero]
    exact ConPolyZono.aux_mem_of_holds cPZ₁ cPZ₂ hE₁ hE₂ a hab hup hlow

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
