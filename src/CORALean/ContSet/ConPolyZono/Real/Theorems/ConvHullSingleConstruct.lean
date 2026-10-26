module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConvHullSingleConsIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullG
public import CORALean.Global.RepBlockDiag
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# What `convHullSingle` denotes

The set of [1, Prop. 9]'s construction applied to one set, before Carathéodory is brought to bear
on it: exactly the weighted sums of `a` of that set's points, with non-negative weights summing to
one.

Both halves are the same two lemmas read in opposite directions: `mem_convHullSingle_cons_iff`
splits the constraints into the copies' own plus the weight row, and `aux_sum_convHullE` reads the
generator sum back as a weighted sum of points. `qI = 0` is [1, Def. 5]'s representation: an
independent generator would answer to no copy.

## Inputs
* `a` – number of weights
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the set is the weighted sums of points of the original

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A weight column names its own factor and nothing else. -/
private theorem ConPolyZono.aux_monomial_cen {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) : -- --- CONCL ---
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
private theorem ConPolyZono.aux_monomial_left {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin h) : -- --- CONCL ---
    PolyZonotope.monomial (ConPolyZono.convHullE a E) v
        (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i))))
      = PolyZonotope.monomial E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullE a E (Fin.castAdd a x)
      (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i)))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ E k i := by
    simp only [ConPolyZono.convHullE, Fin.append_left, Fin.append_right]
    exact prod_repBlockDiag E (fun x => v (Fin.castAdd a x)) j i
  -- the weight rows meet this column at exponent zero
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j')
      ^ ConPolyZono.convHullE a E (Fin.natAdd (a * p) j')
        (Fin.natAdd a (Fin.castAdd (a * h) (finProdFinEquiv (j, i))))) = 1 := by
    simp [ConPolyZono.convHullE]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, mul_one, PolyZonotope.monomial]


/-- A weighted copy column names that monomial times its block's weight. -/
private theorem ConPolyZono.aux_monomial_right {a p h : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin h) : -- --- CONCL ---
    PolyZonotope.monomial (ConPolyZono.convHullE a E) v
        (Fin.natAdd a (Fin.natAdd (a * h) (finProdFinEquiv (j, i))))
      = v (Fin.natAdd (a * p) j) * PolyZonotope.monomial E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullE a E (Fin.castAdd a x)
      (Fin.natAdd a (Fin.natAdd (a * h) (finProdFinEquiv (j, i)))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ E k i := by
    simp only [ConPolyZono.convHullE, Fin.append_left, Fin.append_right]
    exact prod_repBlockDiag E (fun x => v (Fin.castAdd a x)) j i
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


/-- The point of the closed form, as `a` weighted points of the linear
combination — one per block of factors. -/
private theorem ConPolyZono.aux_sum_convHullE {a p h : ℕ} (c : α) (G : Fin h → α)
    (E : Fin p → Fin h → ℕ) (v : Fin (a * p + a) → ℝ) : -- --- CONCL ---
    ((a : ℝ) • c + ∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a E) v i
        • ConPolyZono.convHullG a c G i)
      = ∑ j, (1 + v (Fin.natAdd (a * p) j)) • (c + ∑ i, PolyZonotope.monomial E
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • G i) := by -- --- PROOF ---
  -- the result's own center is `a` copies of the combination's, one per weight
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
    rw [sum_rep (fun y => PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.castAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.castAdd (a * h) y)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [ConPolyZono.aux_monomial_left, ConPolyZono.convHullG, Fin.append_right, Fin.append_left,
      repVec, Equiv.symm_apply_apply]
  -- and the weighted copies, each block's sum scaled by its own weight
  have e3 : (∑ y : Fin (a * h), PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.natAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.natAdd (a * h) y)))
      = ∑ j : Fin a, v (Fin.natAdd (a * p) j) • ∑ i, PolyZonotope.monomial E
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • G i := by
    rw [sum_rep (fun y => PolyZonotope.monomial (ConPolyZono.convHullE a E) v
      (Fin.natAdd a (Fin.natAdd (a * h) y)) • ConPolyZono.convHullG a c G
      (Fin.natAdd a (Fin.natAdd (a * h) y)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ConPolyZono.aux_monomial_right, ConPolyZono.convHullG, Fin.append_right, Fin.append_right,
      repVec, Equiv.symm_apply_apply, smul_smul]
  -- four sums over the same `a` blocks, so one sum of four terms
  rw [Fin.sum_univ_add, Fin.sum_univ_add, e1, e2, e3, hc,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by module


-- =======================================  MAIN THEOREM  ======================================= --

/-- `convHullSingle a` denotes the weighted sums of `a` points of the set. -/
theorem ConPolyZono.convHullSingle_construct (a : ℕ) (cPZ : ConPolyZono α)
    (hq : cPZ.qI = 0) : -- --- CONCL ---
    (cPZ.convHullSingle a).construct
      = {x | ∃ y : Fin a → α, ∃ lam : Fin a → ℝ, (∀ j, y j ∈ cPZ.construct)
        ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ x = ∑ j, lam j • y j} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨v, β, hβ, hsat, rfl⟩
    obtain ⟨hj, hv, hl⟩ := (ConPolyZono.mem_convHullSingle_cons_iff a cPZ v).mp hsat
    refine ⟨fun j => cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • cPZ.G i,
      fun j => 1 + v (Fin.natAdd (a * cPZ.p) j), fun j => ?_, fun j => ?_, ?_, ?_⟩
    · -- block `j` is a factor vector of the set, and its point is that block's
      exact ⟨fun k => v (Fin.castAdd a (finProdFinEquiv (j, k))), fun _ => 0,
        fun _ => by simp, hj j, by simp⟩
    · linarith [abs_le.mp (hv j) |>.1]
    · -- `a` weights shifted by one, over a factor sum the last row pins
      rw [Finset.sum_add_distrib, hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      ring
    · show (a : ℝ) • cPZ.c + (∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a cPZ.E) v i
          • ConPolyZono.convHullG a cPZ.c cPZ.G i) + ∑ j : Fin 0, β j • (Fin.elim0 j : α)
        = _
      rw [ConPolyZono.aux_sum_convHullE]
      simp
  · rintro ⟨y, lam, hy, hlam, hsum, rfl⟩
    choose aj βj hbj hsatj hyj using hy
    -- a weight is at most one, so the factor standing for it stays in the cube
    have hlam1 : ∀ j, lam j ≤ 1 := fun j => by
      rw [← hsum]; exact Finset.single_le_sum (fun i _ => hlam i) (Finset.mem_univ j)
    set v : Fin (a * cPZ.p + a) → ℝ := Fin.append
      (fun x => aj (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
      (fun j => lam j - 1) with hvdef
    have hvblk : ∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) = aj j :=
      fun j => funext fun k => by rw [hvdef, Fin.append_left]; simp
    have hvlam : ∀ j : Fin a, v (Fin.natAdd (a * cPZ.p) j) = lam j - 1 :=
      fun j => by rw [hvdef, Fin.append_right]
    have hGI : ∀ j, (∑ l, βj j l • cPZ.GI l) = (0 : α) := fun j =>
      Finset.sum_eq_zero fun l _ => absurd l.isLt (by omega)
    refine ⟨v, fun _ => 0, fun _ => by simp, ?_, ?_⟩
    · -- each copy carries its own point's factors, and the weights the last row
      refine (ConPolyZono.mem_convHullSingle_cons_iff a cPZ v).mpr ⟨fun j => ?_, fun j => ?_, ?_⟩
      · rw [hvblk j]; exact hsatj j
      · rw [hvlam j, abs_le]; constructor <;> linarith [hlam j, hlam1 j]
      · rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hvlam j),
          Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
    · show (∑ j, lam j • y j) = (a : ℝ) • cPZ.c
        + (∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a cPZ.E) v i
            • ConPolyZono.convHullG a cPZ.c cPZ.G i) + ∑ j : Fin 0, (0 : ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.aux_sum_convHullE]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hyj j, hGI j, add_zero, hvlam j, hvblk j]
      congr 1
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
