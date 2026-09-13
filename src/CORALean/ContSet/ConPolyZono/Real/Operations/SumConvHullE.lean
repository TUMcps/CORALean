import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullG
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.SumRep

/-!
# The generator sum of the convex hull

What [1, Prop. 9]'s generators add up to: a weighted sum of `a` points of the
linear combination, one per block of factors, the weight of block `j` being
`1 + λⱼ` for that block's fresh factor.

The three auxiliary lemmas are the three kinds of column — a weight on its own,
a copy's monomial, and that monomial weighted — and the sum is those three
blocks recombined, `a` copies of the centre absorbed into the result's own.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A weight column names its own factor and nothing else. -/
theorem ConPolyZono.aux_monomial_cen {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) :
    PolyZonotope.monomial (ConPolyZono.convHullE a E) v (Fin.castAdd (a * h + a * h) j)
      = v (Fin.natAdd (a * p) j) := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x)
      ^ ConPolyZono.convHullE a E (Fin.castAdd a x) (Fin.castAdd (a * h + a * h) j)) = 1 := by
    simp [ConPolyZono.convHullE]
  -- among the weight rows only `j`'s own carries a positive power
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j')
      ^ ConPolyZono.convHullE a E (Fin.natAdd (a * p) j') (Fin.castAdd (a * h + a * h) j))
      = v (Fin.natAdd (a * p) j) := by
    simp only [ConPolyZono.convHullE, Fin.append_right, Fin.append_left]
    refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · simp [ConPolyZono.unitCol, Ne.symm hj']
    · simp [ConPolyZono.unitCol]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, one_mul]

/-- A plain copy column names its own block's monomial. -/
theorem ConPolyZono.aux_monomial_left {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin h) :
    PolyZonotope.monomial (ConPolyZono.convHullE a E) v
        (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i))))
      = PolyZonotope.monomial E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullE a E (Fin.castAdd a x)
      (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i)))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ E k i := by
    simp only [ConPolyZono.convHullE, Fin.append_left, Fin.append_right]
    exact ConPolyZono.prod_blkDiag E (fun x => v (Fin.castAdd a x)) j i
  -- the weight rows meet this column at exponent zero
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j')
      ^ ConPolyZono.convHullE a E (Fin.natAdd (a * p) j')
        (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i))))) = 1 := by
    simp [ConPolyZono.convHullE]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, mul_one, PolyZonotope.monomial]

/-- A weighted copy column names that monomial times its block's weight. -/
theorem ConPolyZono.aux_monomial_right {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin h) :
    PolyZonotope.monomial (ConPolyZono.convHullE a E) v
        (Fin.natAdd a (Fin.natAdd (a * h) (finProdFinEquiv (j, i))))
      = v (Fin.natAdd (a * p) j) * PolyZonotope.monomial E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullE a E (Fin.castAdd a x)
      (Fin.natAdd a (Fin.natAdd (a * h) (finProdFinEquiv (j, i)))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ E k i := by
    simp only [ConPolyZono.convHullE, Fin.append_left, Fin.append_right]
    exact ConPolyZono.prod_blkDiag E (fun x => v (Fin.castAdd a x)) j i
  -- here the block's own weight row does carry a power, the others none
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j')
      ^ ConPolyZono.convHullE a E (Fin.natAdd (a * p) j')
        (Fin.natAdd a (Fin.natAdd (a * h) (finProdFinEquiv (j, i)))))
      = v (Fin.natAdd (a * p) j) := by
    simp only [ConPolyZono.convHullE, Fin.append_right, Equiv.symm_apply_apply]
    refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · simp [ConPolyZono.unitCol, Ne.symm hj']
    · simp [ConPolyZono.unitCol]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, mul_comm, PolyZonotope.monomial]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The point of the closed form, as `a` weighted points of the linear
combination — one per block of factors. -/
theorem ConPolyZono.sum_convHullE {a p h : ℕ} (c : α) (G : Fin h → α) (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) :
    ((a : ℝ) • c + ∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a E) v i
        • ConPolyZono.convHullG a c G i)
      = ∑ j, (1 + v (Fin.natAdd (a * p) j)) • (c + ∑ i, PolyZonotope.monomial E
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • G i) := by -- --- PROOF ---
  -- the result's own centre is `a` copies of the combination's, one per weight
  have hc : (a : ℝ) • c = ∑ _j : Fin a, c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact (Nat.cast_smul_eq_nsmul ℝ a c)
  have e1 : (∑ j : Fin a, PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.castAdd (a * h + a * h) j) • ConPolyZono.convHullG a c G
      (Fin.castAdd (a * h + a * h) j)) = ∑ j : Fin a, v (Fin.natAdd (a * p) j) • c :=
    Finset.sum_congr rfl fun j _ => by
      rw [ConPolyZono.aux_monomial_cen, ConPolyZono.convHullG, Fin.append_left]
  -- the plain copies, block by block
  have e2 : (∑ y : Fin (a * h), PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.castAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.castAdd (a * h) y)))
      = ∑ j : Fin a, ∑ i, PolyZonotope.monomial E
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • G i := by
    rw [ConPolyZono.sum_rep (fun y => PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.castAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.castAdd (a * h) y)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [ConPolyZono.aux_monomial_left, ConPolyZono.convHullG, Fin.append_right, Fin.append_left,
      ConPolyZono.repVec, Equiv.symm_apply_apply]
  -- and the weighted copies, each block's sum scaled by its own weight
  have e3 : (∑ y : Fin (a * h), PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.natAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.natAdd (a * h) y)))
      = ∑ j : Fin a, v (Fin.natAdd (a * p) j) • ∑ i, PolyZonotope.monomial E
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • G i := by
    rw [ConPolyZono.sum_rep (fun y => PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.natAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.natAdd (a * h) y)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ConPolyZono.aux_monomial_right, ConPolyZono.convHullG, Fin.append_right, Fin.append_right,
      ConPolyZono.repVec, Equiv.symm_apply_apply, smul_smul]
  -- four sums over the same `a` blocks, so one sum of four terms
  rw [Fin.sum_univ_add, Fin.sum_univ_add, e1, e2, e3, hc,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
