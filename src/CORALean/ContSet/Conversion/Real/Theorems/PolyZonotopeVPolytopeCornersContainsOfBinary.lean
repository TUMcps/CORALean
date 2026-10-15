module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.Global.Corners
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope

@[expose] public section

/-!
# A polynomial zonotope as its corners: `vPolytopeCorners_contains_of_binary`
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corners enclose as soon as no exponent exceeds one, which is what makes
the point multilinear in the factors — and then nothing is lost, as nothing is
lost at a zonotope's corners. -/
theorem PolyZonotope.vPolytopeCorners_contains_of_binary (pZ : PolyZonotope α)
    (hE : ∀ k i, pZ.E k i ≤ 1) :
    pZ.construct ⊆ pZ.vPolytopeCorners.construct := by -- --- PROOF ---
  rintro _ ⟨a, β, ha, hb, rfl⟩
  -- how far from `-1` towards `1` each factor and each coefficient sits
  obtain ⟨t, hta, htb⟩ : ∃ t : Fin (pZ.p + pZ.q) → ℝ,
      (∀ k, t (Fin.castAdd pZ.q k) = (a k + 1) / 2)
        ∧ ∀ j, t (Fin.natAdd pZ.p j) = (β j + 1) / 2 :=
    ⟨Fin.append (fun k => (a k + 1) / 2) fun j => (β j + 1) / 2,
      fun k => Fin.append_left _ _ k, fun j => Fin.append_right _ _ j⟩
  -- and that fraction is in `[0,1]`, both blocks' coefficients being in `[-1,1]`
  have ht0 : ∀ l, 0 ≤ t l := by
    refine Fin.addCases ?_ ?_
    · intro k
      rw [hta k]
      linarith [(abs_le.mp (ha k)).1]
    · intro j
      rw [htb j]
      linarith [(abs_le.mp (hb j)).1]
  have ht1 : ∀ l, t l ≤ 1 := by
    refine Fin.addCases ?_ ?_
    · intro k
      rw [hta k]
      linarith [(abs_le.mp (ha k)).2]
    · intro j
      rw [htb j]
      linarith [(abs_le.mp (hb j)).2]
  have hone : (∑ σ : Fin (pZ.p + pZ.q) → Bool, ∏ l, (if σ l then t l else 1 - t l)) = 1 := by
    rw [sum_prod_bool]
    simp
  -- a sign sums back to its factor's own average, and the monomial with it
  have hmono : ∀ i, (∑ σ : Fin (pZ.p + pZ.q) → Bool,
      (∏ l, (if σ l then t l else 1 - t l)) * PolyZonotope.monomial pZ.E
        (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i)
          = PolyZonotope.monomial pZ.E a i := by
    intro i
    -- what a `-` puts on this column, and `1` for an independent generator
    obtain ⟨V, hVa, hVb⟩ : ∃ V : Fin (pZ.p + pZ.q) → ℝ,
        (∀ k, V (Fin.castAdd pZ.q k) = (-1:ℝ) ^ pZ.E k i) ∧ ∀ j, V (Fin.natAdd pZ.p j) = 1 :=
      ⟨Fin.append (fun k => (-1:ℝ) ^ pZ.E k i) fun _ => (1:ℝ),
        fun k => Fin.append_left _ _ k, fun j => Fin.append_right _ _ j⟩
    -- the monomial is itself a choice of one of two per coordinate
    have hsplit : ∀ σ : Fin (pZ.p + pZ.q) → Bool,
        PolyZonotope.monomial pZ.E (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i
          = ∏ l, (if σ l then (1:ℝ) else V l) := by
      intro σ
      have hone' : (∏ j : Fin pZ.q,
          (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else V (Fin.natAdd pZ.p j))) = 1 :=
        Finset.prod_eq_one fun j _ => by
          rw [hVb j]
          exact ite_self 1
      simp only [PolyZonotope.monomial]
      rw [Fin.prod_univ_add, hone', mul_one]
      exact Finset.prod_congr rfl fun k _ => by
        rw [hVa k]
        cases hσ : σ (Fin.castAdd pZ.q k) <;> simp
    have hstep : ∀ σ : Fin (pZ.p + pZ.q) → Bool,
        (∏ l, (if σ l then t l else 1 - t l)) * PolyZonotope.monomial pZ.E
            (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i
          = (∏ l, (if σ l then t l else 1 - t l)) * ∏ l, (if σ l then (1:ℝ) else V l) :=
      fun σ => by rw [hsplit σ]
    -- an independent generator's coordinate averages away
    have hright : (∏ j : Fin pZ.q, (t (Fin.natAdd pZ.p j) * 1
        + (1 - t (Fin.natAdd pZ.p j)) * V (Fin.natAdd pZ.p j))) = 1 :=
      Finset.prod_eq_one fun j _ => by
        rw [hVb j]
        ring
    -- an exponent of zero or one, which are the two ends of the factor's range
    have hleft : ∀ k, t (Fin.castAdd pZ.q k) * 1
        + (1 - t (Fin.castAdd pZ.q k)) * V (Fin.castAdd pZ.q k) = a k ^ pZ.E k i := by
      intro k
      rw [hVa k, hta k]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hE k i) with h | h <;> rw [h] <;> ring
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ (Finset.univ : Finset (Fin (pZ.p + pZ.q) → Bool)))
        => hstep σ,
      sum_prod_bool_prod t (fun _ => (1:ℝ)) V, Fin.prod_univ_add, hright, mul_one,
      Finset.prod_congr rfl fun k _ => hleft k, PolyZonotope.monomial]
  have hbeta : ∀ j, (∑ σ : Fin (pZ.p + pZ.q) → Bool,
      (∏ l, (if σ l then t l else 1 - t l)) * (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else -1))
        = β j := by
    intro j
    rw [sum_prod_bool_mul t (fun _ => 1) (fun _ => -1) (Fin.natAdd pZ.p j), htb j]
    ring
  -- one corner's contribution, split into center, dependent and independent parts
  have hR : ∀ σ : Fin (pZ.p + pZ.q) → Bool,
      (∏ l, (if σ l then t l else 1 - t l)) • pZ.corner σ
        = (∏ l, (if σ l then t l else 1 - t l)) • pZ.c
          + ∑ i, ((∏ l, (if σ l then t l else 1 - t l)) * PolyZonotope.monomial pZ.E
              (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i) • pZ.G i
          + ∑ j, ((∏ l, (if σ l then t l else 1 - t l))
              * (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else -1)) • pZ.GI j := by
    intro σ
    rw [PolyZonotope.corner, smul_add, smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [smul_smul]
  -- each generator's own coefficient sums back, the other coordinates averaging away
  have hdep : (∑ σ : Fin (pZ.p + pZ.q) → Bool, ∑ i,
      ((∏ l, (if σ l then t l else 1 - t l)) * PolyZonotope.monomial pZ.E
        (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i) • pZ.G i)
          = ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_smul, hmono i]
  have hind : (∑ σ : Fin (pZ.p + pZ.q) → Bool, ∑ j,
      ((∏ l, (if σ l then t l else 1 - t l))
        * (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else -1)) • pZ.GI j)
          = ∑ j, β j • pZ.GI j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_smul, hbeta j]
  -- a corner's convex weight is the product of the per-coordinate ones
  refine ⟨fun v => ∏ l, (if signEquiv (pZ.p + pZ.q) v l then t l else 1 - t l),
    fun v => ?_, ?_, ?_⟩
  · exact Finset.prod_nonneg fun l _ => by
      cases signEquiv (pZ.p + pZ.q) v l <;> simp <;> linarith [ht0 l, ht1 l]
  · -- the weights sum to the product of the per-coordinate sums, which is `1`
    show ∑ v : Fin (2 ^ (pZ.p + pZ.q)),
        (∏ l, (if signEquiv (pZ.p + pZ.q) v l then t l else 1 - t l)) = 1
    rw [Fintype.sum_equiv (signEquiv (pZ.p + pZ.q))
        (fun v => ∏ l, (if signEquiv (pZ.p + pZ.q) v l then t l else 1 - t l))
        (fun σ => ∏ l, (if σ l then t l else 1 - t l)) fun _ => rfl]
    exact hone
  · -- and weighting the corners by them reproduces the point
    show pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, β j • pZ.GI j
        = ∑ v : Fin (2 ^ (pZ.p + pZ.q)),
            (∏ l, (if signEquiv (pZ.p + pZ.q) v l then t l else 1 - t l))
              • pZ.corner (signEquiv (pZ.p + pZ.q) v)
    rw [Fintype.sum_equiv (signEquiv (pZ.p + pZ.q))
        (fun v => (∏ l, (if signEquiv (pZ.p + pZ.q) v l then t l else 1 - t l))
          • pZ.corner (signEquiv (pZ.p + pZ.q) v))
        (fun σ : Fin (pZ.p + pZ.q) → Bool => (∏ l, (if σ l then t l else 1 - t l)) • pZ.corner σ)
        fun _ => rfl,
      Finset.sum_congr rfl fun σ (_ : σ ∈ (Finset.univ : Finset (Fin (pZ.p + pZ.q) → Bool)))
        => hR σ,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, hone, one_smul,
      hdep, hind]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
