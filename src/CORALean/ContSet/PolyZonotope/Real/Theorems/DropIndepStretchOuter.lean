module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DropIndepStretch
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
public import CORALean.Global.Partition
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `dropIndepStretch` over-approximates the generator it drops

[1, Prop. 2]. `hk` and `hE` are what makes the `n` picked dependent generators
usable as a private basis: `hk` keeps their factors distinct and `hE` keeps
each picked factor exclusive to its own generator — the `(k j, partD.left j)`
entry of `E` is `1` and every other entry in that row or that column is `0` —
which is exactly what lets `a` be nudged at those `n` factors alone without
disturbing any other generator's monomial. `hPinv` is what recovers `γ = P⁻¹
g^{(i)}` afterwards: `P *ᵥ γ = g^{(i)}` is the one place it is spent.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Different sides of the same partition never coincide. -/
theorem PolyZonotope.aux_dropIndep_ne {h r n : ℕ} (partD : Split (Fin h) into (Fin n) ⊕ (Fin r))
    (j : Fin n) (j' : Fin r) : partD.right j' ≠ partD.left j := by
  simp only [Partition.right, Partition.left, Partition.on, ne_eq]
  intro heq
  have hs := partD.index.injective heq
  simp at hs


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.dropIndepStretch_outer {n : ℕ} (pZ : PolyZonotope (Vec ℝ n)) {r dI : ℕ}
    (partD : Split (Fin pZ.h) into (Fin n) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin 1))
    (k : Fin n → Fin pZ.p) (hk : Function.Injective k)
    (hE : ∀ j k' l, (k' = k j ∨ l = partD.left j) →
      pZ.E k' l = if k' = k j ∧ l = partD.left j then 1 else 0)
    (hPinv : IsUnit (pZ.dropIndepMat partD).det) :
    pZ.construct ⊆ (pZ.dropIndepStretch partD partI).construct := by -- --- PROOF ---
  set P := pZ.dropIndepMat partD with hPdef
  set i0 := partI.right 0 with hi0def
  set γ : Fin n → ℝ := P⁻¹ *ᵥ pZ.GI i0 with hγdef
  -- every entry in a picked row or column is the diagonal entry alone
  have hzero_row : ∀ j l, l ≠ partD.left j → pZ.E (k j) l = 0 := fun j l hl => by
    rw [hE j (k j) l (Or.inl rfl), if_neg fun h => hl h.2]
  have hzero_col : ∀ j k', k' ≠ k j → pZ.E k' (partD.left j) = 0 := fun j k' hk' => by
    rw [hE j k' (partD.left j) (Or.inr rfl), if_neg fun h => hk' h.1]
  -- a picked generator's monomial is bare `b (k j)`, at either factor vector
  have hmono : ∀ (b : Fin pZ.p → ℝ) (j : Fin n),
      PolyZonotope.monomial pZ.E b (partD.left j) = b (k j) := by
    intro b j
    rw [PolyZonotope.monomial, Finset.prod_eq_single (k j)
      (fun k' _ hk' => by rw [hzero_col j k' hk', pow_zero])
      (fun h => absurd (Finset.mem_univ _) h),
      hE j (k j) (partD.left j) (Or.inl rfl), if_pos ⟨rfl, rfl⟩, pow_one]
  -- unpicked generators never see a picked factor
  have hunpicked : ∀ j' : Fin r, ∀ j, pZ.E (k j) (partD.right j') = 0 :=
    fun j' j => hzero_row j (partD.right j') (PolyZonotope.aux_dropIndep_ne partD j j')
  intro x hx
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hx
  rw [PolyZonotope.mem_construct_iff]
  -- the compensated factor vector: nudged at the `n` picked factors alone
  set a' : Fin pZ.p → ℝ := fun k' =>
    if h : ∃ j, k' = k j then (a k' + β i0 * γ h.choose) / (1 + |γ h.choose|) else a k'
    with ha'def
  have ha'k : ∀ j, a' (k j) = (a (k j) + β i0 * γ j) / (1 + |γ j|) := by
    intro j
    have hex : ∃ j0, k j = k j0 := ⟨j, rfl⟩
    have hj0 : hex.choose = j := (hk hex.choose_spec).symm
    show (if h : ∃ j0, k j = k j0 then (a (k j) + β i0 * γ h.choose) / (1 + |γ h.choose|)
        else a (k j)) = _
    rw [dif_pos hex, hj0]
  have hbound : ∀ j : Fin n, |a (k j) + β i0 * γ j| ≤ 1 + |γ j| := by
    intro j
    calc |a (k j) + β i0 * γ j| ≤ |a (k j)| + |β i0 * γ j| := abs_add_le _ _
      _ = |a (k j)| + |β i0| * |γ j| := by rw [abs_mul]
      _ ≤ 1 + 1 * |γ j| := by gcongr; exacts [ha (k j), hβ i0]
      _ = 1 + |γ j| := by ring
  -- the new factor vector stays inside the box
  have ha' : ∀ k', |a' k'| ≤ 1 := by
    intro k'
    by_cases hex : ∃ j, k' = k j
    · obtain ⟨j, hj⟩ := hex
      subst hj
      rw [ha'k j, abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + |γ j|),
        div_le_one (by positivity)]
      exact hbound j
    · show |if h : ∃ j, k' = k j then _ else a k'| ≤ 1
      rw [dif_neg hex]
      exact ha k'
  -- the kept independent coefficients: `β` restricted off `i0`
  refine ⟨a', fun l => β (partI.left l), ha', fun l => hβ (partI.left l), fun i => ?_⟩
  have hkey : P *ᵥ γ = pZ.GI i0 := by
    rw [hγdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPinv, Matrix.one_mulVec]
  have hPcol : ∀ j, P i j = pZ.G (partD.left j) i := fun j => rfl
  have hcompensate : ∑ j, P i j * γ j = pZ.GI i0 i := congrFun hkey i
  rw [hx i]
  -- split both `l`-sums along `partD`, and the `GI`-sums of `x` and the target along `partI`
  rw [show (∑ l, pZ.G l i * PolyZonotope.monomial pZ.E a l)
      = ∑ j, pZ.G (partD.left j) i * PolyZonotope.monomial pZ.E a (partD.left j)
        + ∑ j', pZ.G (partD.right j') i * PolyZonotope.monomial pZ.E a (partD.right j')
      from partD.sum_split₂ (fun l => pZ.G l i * PolyZonotope.monomial pZ.E a l)]
  rw [show (∑ j, pZ.GI j i * β j)
      = ∑ l, pZ.GI (partI.left l) i * β (partI.left l)
        + pZ.GI i0 i * β i0
      from by
        rw [partI.sum_split₂ (fun j => pZ.GI j i * β j)]
        congr 1
        exact Fin.sum_univ_one _]
  -- the target, unfolded to the same split shape as `hx i` above
  show pZ.c i +
      ((∑ j, pZ.G (partD.left j) i * PolyZonotope.monomial pZ.E a (partD.left j))
        + ∑ j', pZ.G (partD.right j') i * PolyZonotope.monomial pZ.E a (partD.right j'))
      + ((∑ l, pZ.GI (partI.left l) i * β (partI.left l)) + pZ.GI i0 i * β i0)
    = (pZ.dropIndepStretch partD partI).c i
      + (∑ l, (pZ.dropIndepStretch partD partI).G l i
          * PolyZonotope.monomial pZ.E a' l)
      + ∑ l, (pZ.dropIndepStretch partD partI).GI l i * β (partI.left l)
  -- `c` and `GI` are untouched; only `G` moved, and only at the `n` picked indices
  have hGIeq : ∀ l, (pZ.dropIndepStretch partD partI).GI l = pZ.GI (partI.left l) := fun _ => rfl
  simp only [hGIeq]
  rw [show (pZ.dropIndepStretch partD partI).c i = pZ.c i from rfl,
    show (∑ l, (pZ.dropIndepStretch partD partI).G l i * PolyZonotope.monomial pZ.E a' l)
        = ∑ j, (pZ.dropIndepStretch partD partI).G (partD.left j) i
            * PolyZonotope.monomial pZ.E a' (partD.left j)
          + ∑ j', (pZ.dropIndepStretch partD partI).G (partD.right j') i
              * PolyZonotope.monomial pZ.E a' (partD.right j')
      from partD.sum_split₂
        (fun l => (pZ.dropIndepStretch partD partI).G l i * PolyZonotope.monomial pZ.E a' l)]
  -- which side of `partD` an index came from, read back through `partD.index`
  have hsymmL : ∀ j : Fin n,
      partD.index.symm (partD.left j) = (⟨true, j⟩ : Σ b, Pair (Fin n) (Fin r) b) :=
    fun j => partD.index.symm_apply_apply ⟨true, j⟩
  have hsymmR : ∀ j' : Fin r,
      partD.index.symm (partD.right j') = (⟨false, j'⟩ : Σ b, Pair (Fin n) (Fin r) b) :=
    fun j' => partD.index.symm_apply_apply ⟨false, j'⟩
  -- a picked generator is the stretched one; every other generator is untouched
  have hGleft : ∀ j, (pZ.dropIndepStretch partD partI).G (partD.left j)
      = (1 + |γ j|) • pZ.G (partD.left j) := by
    intro j
    show (match partD.index.symm (partD.left j) with
      | ⟨true, j0⟩ => (1 + |γ j0|) • pZ.G (partD.left j)
      | ⟨false, _⟩ => pZ.G (partD.left j)) = _
    rw [hsymmL j]
  have hGright : ∀ j' : Fin r, (pZ.dropIndepStretch partD partI).G (partD.right j')
      = pZ.G (partD.right j') := by
    intro j'
    show (match partD.index.symm (partD.right j') with
      | ⟨true, j0⟩ => (1 + |γ j0|) • pZ.G (partD.right j')
      | ⟨false, _⟩ => pZ.G (partD.right j')) = _
    rw [hsymmR j']
  simp only [hGleft, hGright, Pi.smul_apply, smul_eq_mul]
  -- each picked generator's monomial, read off `hmono`, at either factor vector
  have hmono_left_a' : ∀ j, PolyZonotope.monomial pZ.E a' (partD.left j) = a' (k j) := hmono a'
  have hmono_left_a : ∀ j, PolyZonotope.monomial pZ.E a (partD.left j) = a (k j) := hmono a
  have hmono_right_a' : ∀ j' : Fin r,
      PolyZonotope.monomial pZ.E a' (partD.right j')
        = PolyZonotope.monomial pZ.E a (partD.right j') := by
    intro j'
    rw [PolyZonotope.monomial, PolyZonotope.monomial]
    refine Finset.prod_congr rfl fun k' _ => ?_
    by_cases hk' : ∃ j, k' = k j
    · obtain ⟨j, rfl⟩ := hk'
      rw [hunpicked j' j, pow_zero, pow_zero]
    · rw [ha'def]
      simp only [dif_neg hk']
  simp only [hmono_left_a', hmono_left_a, hmono_right_a', ha'k]
  -- undo the stretch: back to plain `a`, plus the compensating share of `g^{(i)}`
  have hstep : ∀ j,
      (1 + |γ j|) * pZ.G (partD.left j) i * ((a (k j) + β i0 * γ j) / (1 + |γ j|))
        = pZ.G (partD.left j) i * a (k j) + β i0 * (γ j * pZ.G (partD.left j) i) := by
    intro j
    have hpos : (1:ℝ) + |γ j| ≠ 0 := by positivity
    field_simp
  simp only [hstep, Finset.sum_add_distrib]
  have hγsum : ∑ j, β i0 * (γ j * pZ.G (partD.left j) i) = β i0 * pZ.GI i0 i := by
    rw [← hcompensate, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPcol j]; ring
  rw [hγsum, mul_comm (pZ.GI i0 i) (β i0)]
  -- pure regrouping now, the coefficient algebra already done above
  show pZ.c i +
        (∑ x, pZ.G (partD.left x) i * a (k x) +
          ∑ j', pZ.G (partD.right j') i * PolyZonotope.monomial pZ.E a (partD.right j')) +
      (∑ l, pZ.GI (partI.left l) i * β (partI.left l) + β i0 * pZ.GI i0 i) =
    pZ.c i +
        (∑ x, pZ.G (partD.left x) i * a (k x) + β i0 * pZ.GI i0 i +
          ∑ j', pZ.G (partD.right j') i * PolyZonotope.monomial pZ.E a (partD.right j')) +
      ∑ l, pZ.GI (partI.left l) i * β (partI.left l)
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
