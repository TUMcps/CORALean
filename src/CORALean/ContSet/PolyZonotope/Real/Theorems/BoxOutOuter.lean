module

public import CORALean.ContSet.PolyZonotope.Real.Operations.BoxOut
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# Boxing out generators encloses

Removing any dependent generators and appending the diagonal box of their absolute values, widened
by any independent generators' (which `outerApprox` keeps as well), encloses every point of the
original at the same factor vector: a monomial of `a ∈ [-1,1]ᵖ` is at most one in absolute value,
and `Zonotope.coefficient` rescales into the box, the degenerate radius `0` included. The enclosure
holds for any choice of the removed generators, which is what lets `outerApprox`'s scan be a
heuristic. It is not an equality: the box is larger than what the removed generators reach.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `boxOut`'s independent generator count, through the projection. -/
theorem PolyZonotope.aux_sum_univ_boxOut_q {pZ : PolyZonotope (Vec ℝ n)} {removed : Fin pZ.h → Prop}
    {taken : Fin pZ.q → Prop} [DecidablePred removed] [DecidablePred taken]
    (f : Fin (pZ.q + n) → ℝ) : -- --- CONCL ---
    ∑ j : Fin (pZ.boxOut removed taken).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The dependent generator count of `boxOut`, read back at the kept ones. -/
theorem PolyZonotope.aux_sum_univ_boxOut_h {pZ : PolyZonotope (Vec ℝ n)} {removed : Fin pZ.h → Prop}
    {taken : Fin pZ.q → Prop} [DecidablePred removed] [DecidablePred taken]
    (f : Fin (Fintype.card {i : Fin pZ.h // ¬ removed i}) → ℝ) :
    ∑ l : Fin (pZ.boxOut removed taken).h, f l = ∑ l, f l :=
  rfl

/-- What the removed dependent generators reach in a coordinate is at most their absolute sum. -/
theorem PolyZonotope.aux_abs_removed_le (pZ : PolyZonotope (Vec ℝ n)) {r : ℕ}
    (right : Fin r → Fin pZ.h) {a : Fin pZ.p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, pZ.G (right l) i * PolyZonotope.monomial pZ.E a (right l)|
      ≤ ∑ l, |pZ.G (right l) i| := by -- --- PROOF ---
  -- the absolute value of a sum, then each monomial is at most one
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (PolyZonotope.abs_monomial_le_one pZ.E ha (right l))
    (abs_nonneg (pZ.G (right l) i))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing out any dependent generators, and widening the box by any independent ones, encloses. -/
theorem PolyZonotope.boxOut_outer (pZ : PolyZonotope (Vec ℝ n)) (removed : Fin pZ.h → Prop)
    (taken : Fin pZ.q → Prop) [DecidablePred removed] [DecidablePred taken] :
    pZ.construct ⊆ (pZ.boxOut removed taken).construct := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hxmem
  set part := Partition.ofPred removed with hpart
  -- the removed dependent generators reach `D i` in coordinate `i`, the box has radius `R i`
  set D : Fin n → ℝ := fun i =>
    ∑ l, pZ.G (part.right l) i * PolyZonotope.monomial pZ.E a (part.right l) with hD
  set R : Fin n → ℝ := fun k =>
    (∑ i, if removed i then |pZ.G i k| else 0) + ∑ j, if taken j then |pZ.GI j k| else 0
    with hR
  have hsplit : ∀ k, (∑ i, if removed i then |pZ.G i k| else 0)
      = ∑ l, |pZ.G (part.right l) k| := fun k => by
    rw [part.sum_split₂ fun i => if removed i then |pZ.G i k| else 0]
    have h1 : ∀ l, (if removed (part.left l) then |pZ.G (part.left l) k| else 0) = 0 :=
      fun l => if_neg (Partition.ofPred_left removed l)
    have h2 : ∀ l, (if removed (part.right l) then |pZ.G (part.right l) k| else 0)
        = |pZ.G (part.right l) k| := fun l => if_pos (Partition.ofPred_right removed l)
    simp only [h1, h2, Finset.sum_const_zero, zero_add]
  -- the removed generators stay inside the box
  have hbound : ∀ i, |D i| ≤ R i := fun i => by
    have h1 := PolyZonotope.aux_abs_removed_le pZ part.right ha i
    have h2 : 0 ≤ ∑ j, if taken j then |pZ.GI j i| else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> simp
    have h3 : (∑ l, |pZ.G (part.right l) i|) ≤ R i := by
      rw [hR]; dsimp only; rw [hsplit i]; linarith
    exact h1.trans h3
  have hnonneg : ∀ i, (0 : ℝ) ≤ R i := fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: the same factors, the same coefficients, and one per coordinate for the box
  refine PolyZonotope.mem_construct_iff.mpr
    ⟨a, Fin.append β (fun i => Zonotope.coefficient (R i) (D i)), ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ j
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  -- the value: the kept columns unchanged, the removed ones inside the box
  · rw [hx i, part.sum_split₂ fun l => pZ.G l i * PolyZonotope.monomial pZ.E a l]
    rw [PolyZonotope.aux_sum_univ_boxOut_q, PolyZonotope.aux_sum_univ_boxOut_h]
    simp only [PolyZonotope.boxOut, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]
    rw [← hpart]
    show _ = pZ.c i + ∑ x, pZ.G (part.left x) i * PolyZonotope.monomial pZ.E a (part.left x)
      + (∑ j, pZ.GI j i * β j + D i)
    rw [hD]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
