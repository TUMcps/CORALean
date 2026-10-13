import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
import CORALean.Global.Corners

/-!
# A polynomial zonotope as its corners

Two enclosures, the cheaper first. `vPolytope` goes through the zonotope
enclosure and then that zonotope's `2ʰ` sign corners, losing whatever the
zonotope step lost and nothing further.

`vPolytopeSplit` is [1, Prop. 6], which splits the exponent matrix instead. A
column whose exponents are all at most one is multilinear in the factors, and a
multilinear map on a box is a convex combination of its values at the box's
corners — so such a column is read at every sign vector of the factors exactly.
Only a column with an exponent above one is given up, to `zonotopeEven`. That is
all the vertex enumeration the paper defers to a companion algorithm comes to
here: its closing convex hull only drops points that are not vertices.

Neither is exact, a polynomial zonotope being generally non-convex. The paper
deletes the columns it gives up; here they stay at a zero generator, which costs
vertices and not precision.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def PolyZonotope.vPolytope (pZ : PolyZonotope α) : VPolytope α :=
  pZ.zonotope.vPolytope

theorem PolyZonotope.vPolytope_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.vPolytope.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.vPolytope_contains _)

/-- The vertex a choice of sign picks out, one sign per factor and then one per
independent generator. -/
def PolyZonotope.corner (pZ : PolyZonotope α) (σ : Fin (pZ.p + pZ.q) → Bool) : α :=
  pZ.c
    + ∑ i, PolyZonotope.monomial pZ.E
        (fun k => if σ (Fin.castAdd pZ.q k) then (1:ℝ) else -1) i • pZ.G i
    + ∑ j, (if σ (Fin.natAdd pZ.p j) then (1:ℝ) else -1) • pZ.GI j

noncomputable def PolyZonotope.vPolytopeCorners (pZ : PolyZonotope α) : VPolytope α where
  k := 2 ^ (pZ.p + pZ.q)
  V := fun v => pZ.corner (signEquiv (pZ.p + pZ.q) v)

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
  -- one corner's contribution, split into centre, dependent and independent parts
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The paper's `H` block, read column by column: a column with no exponent above
one is zeroed rather than deleted, so the index set stays `Fin pZ.h`. -/
def PolyZonotope.aux_high (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := 0
  G := fun i => if ∀ k, pZ.E k i ≤ 1 then 0 else pZ.G i
  E := pZ.E
  GI := pZ.GI

/-- The paper's `PZ̄`: what `H` reaches is made independent, through the tight
zonotope enclosure of [1, Prop. 5], and `K` keeps its exponents. -/
noncomputable def PolyZonotope.aux_binarize (pZ : PolyZonotope α) : PolyZonotope α :=
  let H := pZ.aux_high.zonotopeEven                       -- [1, Prop. 5]'s tight enclosure of H
  { p := pZ.p
    h := pZ.h
    q := pZ.h + pZ.q
    c := pZ.c + H.c
    G := fun i => if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0
    E := fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0
    GI := H.G }

theorem PolyZonotope.aux_binarize_E_le (pZ : PolyZonotope α) (k : Fin pZ.aux_binarize.p)
    (i : Fin pZ.aux_binarize.h) : pZ.aux_binarize.E k i ≤ 1 := by
  show (if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) ≤ 1
  split_ifs with h
  · exact h k
  · exact Nat.zero_le 1

theorem PolyZonotope.aux_binarize_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.aux_binarize.construct := by -- --- PROOF ---
  rintro _ ⟨a, β, ha, hb, rfl⟩
  -- what the given-up columns and the independent block reach is a zonotope's
  have hmem : (0 : α) + ∑ i, PolyZonotope.monomial pZ.E a i
        • (if ∀ k, pZ.E k i ≤ 1 then (0:α) else pZ.G i)
      + ∑ j, β j • pZ.GI j ∈ pZ.aux_high.construct := ⟨a, β, ha, hb, rfl⟩
  obtain ⟨γ, hγ, hγeq⟩ := pZ.aux_high.zonotopeEven_contains hmem
  rw [zero_add] at hγeq
  refine ⟨a, γ, ha, hγ, ?_⟩
  -- every column lands in exactly one of the two blocks
  have hsplit : ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
      = ∑ i, PolyZonotope.monomial (fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) a i
            • (if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0)
        + ∑ i, PolyZonotope.monomial pZ.E a i
            • (if ∀ k, pZ.E k i ≤ 1 then (0:α) else pZ.G i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hbin : ∀ k, pZ.E k i ≤ 1
    · -- a kept column keeps its exponents, so its monomial is the one it had
      rw [if_pos hbin, if_pos hbin, smul_zero, add_zero]
      exact congrArg (· • pZ.G i)
        (Finset.prod_congr rfl fun k _ => congrArg (a k ^ ·) (if_pos hbin).symm)
    · rw [if_neg hbin, if_neg hbin, smul_zero, zero_add]
  show pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, β j • pZ.GI j
      = pZ.c + pZ.aux_high.zonotopeEven.c
        + ∑ i, PolyZonotope.monomial (fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) a i
            • (if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0)
        + ∑ l, γ l • pZ.aux_high.zonotopeEven.G l
  rw [hsplit, add_assoc, add_assoc, hγeq]
  abel

/-- [1, Prop. 6]'s `poly`: the corners of `aux_binarize`, which keeps every
column the zonotope enclosure of `vPolytope` would have freed. -/
noncomputable def PolyZonotope.vPolytopeSplit (pZ : PolyZonotope α) : VPolytope α :=
  pZ.aux_binarize.vPolytopeCorners


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.vPolytopeSplit_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.vPolytopeSplit.construct :=
  subset_trans pZ.aux_binarize_contains
    (PolyZonotope.vPolytopeCorners_contains_of_binary _ pZ.aux_binarize_E_le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
