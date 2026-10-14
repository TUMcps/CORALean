module

public import CORALean.ContSet.Taylm.Real.Operations.OptBernstein
public import CORALean.ContSet.Taylm.Real.Theorems.BernsteinBasisNonneg
public import CORALean.ContSet.Taylm.Real.Theorems.LeBernsteinDegree
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfEqSumBernsteinCoeff
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.SumBernsteinBasis

@[expose] public section

/-!
# `optBernstein` encloses

Outer: on the box, a function a Taylor model encloses lies between the least coefficient plus the
remainder's lower end and the greatest coefficient plus its upper end [2]. The polynomial is a
convex combination of its Bernstein coefficients [1], the weights being products of Bernstein
basis polynomials, which are nonnegative on `[0, 1]` and sum to one (`sum_bernsteinBasis`).
Not exact: the coefficients' hull contains the range, with equality only where the polynomial
attains its extreme coefficients, as at the corners of a multilinear one.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
* [2] `contSet/@taylm/optBernstein.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBernstein_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    T.optBernstein.1 ≤ f t ∧ f t ≤ T.optBernstein.2 := by -- --- PROOF ---
  set N := T.bernsteinDegree with hN
  set B := Taylm.bernsteinCoeff T.terms N with hB
  set w : (Fin n → Fin (N + 1)) → ℝ := fun β =>
    ∏ k, Taylm.bernsteinBasis N (β k) ((t k + 1) / 2) with hw
  -- the polynomial is the weighted sum of the coefficients
  have hpoly : T.poly t = ∑ β, B β * w β :=
    Taylm.polyOf_eq_sum_bernsteinCoeff T.terms N (fun a ha k => Taylm.le_bernsteinDegree T ha k) t
  -- the weights are a convex combination
  have hu : ∀ k, 0 ≤ (t k + 1) / 2 ∧ (t k + 1) / 2 ≤ 1 := fun k => by
    have := abs_le.mp (ht k)
    constructor <;> linarith [this.1, this.2]
  have hw0 : ∀ β, 0 ≤ w β := fun β =>
    Finset.prod_nonneg fun k _ => Taylm.bernsteinBasis_nonneg N _ (hu k).1 (hu k).2
  have hone : ∀ k, ∑ j : Fin (N + 1), Taylm.bernsteinBasis N j ((t k + 1) / 2) = 1 := fun k => by
    rw [← Finset.sum_range (fun j => Taylm.bernsteinBasis N j ((t k + 1) / 2))]
    exact Taylm.sum_bernsteinBasis N _
  have hw1 : ∑ β, w β = 1 := by
    have hprod := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin (N + 1))))
      (fun k j => Taylm.bernsteinBasis N j ((t k + 1) / 2))
    rw [Fintype.piFinset_univ] at hprod
    rw [← hprod]
    exact Finset.prod_eq_one fun k _ => hone k
  -- so the polynomial lies between the least and greatest coefficient
  have hlo : Finset.univ.inf' ⟨fun _ => 0, Finset.mem_univ _⟩ B ≤ T.poly t := by
    rw [hpoly]
    calc Finset.univ.inf' ⟨fun _ => 0, Finset.mem_univ _⟩ B
        = ∑ β, Finset.univ.inf' ⟨fun _ => 0, Finset.mem_univ _⟩ B * w β := by
          rw [← Finset.mul_sum, hw1, mul_one]
      _ ≤ ∑ β, B β * w β := Finset.sum_le_sum fun β _ =>
          mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ β)) (hw0 β)
  have hhi : T.poly t ≤ Finset.univ.sup' ⟨fun _ => 0, Finset.mem_univ _⟩ B := by
    rw [hpoly]
    calc ∑ β, B β * w β
        ≤ ∑ β, Finset.univ.sup' ⟨fun _ => 0, Finset.mem_univ _⟩ B * w β :=
          Finset.sum_le_sum fun β _ =>
            mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ β)) (hw0 β)
      _ = Finset.univ.sup' ⟨fun _ => 0, Finset.mem_univ _⟩ B := by
          rw [← Finset.mul_sum, hw1, mul_one]
  -- and the remainder encloses the difference
  have hr := h t ht
  simp only [Taylm.optBernstein]
  constructor <;> linarith [hr.1, hr.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
