module

public import CORALean.Global.IpmExistsSubsetCardEq
public import CORALean.Global.IpmSolCongr
public import CORALean.Global.MeasureProdViolationLt
public import CORALean.Global.MapProdPiOfIndep
public import CORALean.Global.IndepPointOfMDependent
public import CORALean.Global.ExistsSeparatedCardEq

@[expose] public section

/-!
# The reliability of an interval predictor model from `M`-dependent data

[1, Thm. 4], corrected: for a strictly stationary sequence `x(t) = (ϕ(t), y(t))` with marginal `P`,
`M`-dependent in the sense of Bosq, and Problem 1′ as in [1, Thm. 3], `Prob{R(Î^A_{N,k}) ≥ 1 - ε} >
1 - β` with `β = C(N, d) Σ_{i=0}^k C(W, i) εⁱ(1 - ε)^{W-i}`, `W = ⌈(N - d(2M + 1))/(M + 1)⌉`.
Printed with pairwise independence (Def. 5) it is false (`ipmReliabilityMDependent_counterexample`).
The proof is that of [1, Thm. 3], with the other points replaced by `W` of them more than `M` apart
from each other and from the `d` determining ones (`exists_separated_card_eq`), independent of the
others kept (`indep_point_of_mDependent`), so their joint law is `law(x_H) ⊗ P^W`
(`map_prod_pi_eq_of_indep`).

## References

* [1] [M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica,
      2009.](../../../references/2009/campi-automatica-interval-predictor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory

variable {E Φ Y : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {N d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the binomial probabilities sum to `1`
private theorem aux_binom_sum_eq_one {W k : ℕ} (hWk : W ≤ k) (ε : ℝ) : -- --- CONCL ---
    ∑ i ∈ Finset.range (k + 1), (W.choose i : ℝ) * ε ^ i * (1 - ε) ^ (W - i) =
      1 := by -- --- PROOF ---
  -- the terms above `W` vanish, the rest is `(ε + (1 - ε))^W`
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show W + 1 ≤ k + 1 by omega))
    fun i _ hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [Nat.choose_eq_zero_of_lt (show W < i by omega)]]
  have h := add_pow ε (1 - ε) W
  rw [add_sub_cancel, one_pow] at h
  exact (Finset.sum_congr rfl fun i _ => by ring).trans h.symm

-- `C(N, d) ≥ 2` for `0 < d < N`
private theorem aux_two_le_choose {N d : ℕ} (h1 : 1 ≤ d) (h2 : d < N) : -- --- CONCL ---
    2 ≤ N.choose d := by -- --- PROOF ---
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have : 0 < n.choose e := Nat.choose_pos (by omega)
  have : 0 < n.choose (e + 1) := Nat.choose_pos (by omega)
  omega

-- a family's σ-algebra is the join of its members'
private theorem aux_comap_pi_le {Ω κ Δ : Type} [MeasurableSpace Δ] (f : κ → Ω → Δ)
    {m : MeasurableSpace Ω} (h : ∀ i, MeasurableSpace.comap (f i) inferInstance ≤ m) :
    MeasurableSpace.comap (fun ω i => f i ω) inferInstance ≤ m := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact iSup_le fun i => by rw [MeasurableSpace.comap_comp]; exact h i

-- a value at a time of `S` is measurable in the σ-algebra of the values at `S`
private theorem aux_comap_le_values {Ω Δ : Type} [MeasurableSpace Δ] (x : ℕ → Ω → Δ) (S : Finset ℕ)
    {t : ℕ} (ht : t ∈ S) :
    MeasurableSpace.comap (x t) inferInstance ≤
      MeasurableSpace.comap (fun ω (s : S) => x s ω) inferInstance := by
  have : x t = (fun f : S → Δ => f ⟨t, ht⟩) ∘ fun ω (s : S) => x s ω := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
theorem ipm_reliability_mDependent [MeasurableSpace E] [MeasurableSpace Φ] [MeasurableSpace Y]
    {Ω : Type} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (x : ℕ → Ω → Φ × Y) (hx : ∀ t, Measurable (x t)) (P : Measure (Φ × Y))
    (hstat : ∀ n s, ℙ.map (fun ω (i : Fin n) => x (i + s) ω) = ℙ.map (fun ω (i : Fin n) => x i ω))
    (hP : ℙ.map (x 0) = P) {M : ℕ}
    -- `M`-dependence (Bosq): past and future more than `M` apart are independent
    (hM : ∀ L R : Finset ℕ, (∀ l ∈ L, ∀ r ∈ R, l + M < r) →
      IndepFun (fun ω (l : L) => x l ω) (fun ω (r : R) => x r ω) ℙ)
    (hd : Module.finrank ℝ E = d) {k : ℕ} (hk : k < N - d) (𝒬 : Set E) (μQ : E → ℝ)
    (hμ : ConvexOn ℝ 𝒬 μQ) (I : E → Φ → Set Y) (hI : ∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ})
    (sol : Finset (Fin N) → (Fin N → Φ × Y) → E)
    (hsol : ∀ F X, d ≤ F.card → sol F X ∈ 𝒬 ∧ (∀ t ∈ F, (X t).2 ∈ I (sol F X) (X t).1) ∧
      ∀ Q ∈ 𝒬, (∀ t ∈ F, (X t).2 ∈ I Q (X t).1) → Q ≠ sol F X → μQ (sol F X) < μQ Q)
    (A : (Fin N → Φ × Y) → Finset (Fin N)) (hA : ∀ X, (A X).card = N - k)
    (hIm : MeasurableSet {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1})
    (hsolm : ∀ H : Finset (Fin N), H.card = d → Measurable (sol H)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) : -- --- CONCL ---
    1 - (N.choose d : ℝ) * ∑ i ∈ Finset.range (k + 1),
        ((⌈((N : ℝ) - d * (2 * M + 1)) / (M + 1)⌉₊).choose i : ℝ) * ε ^ i *
          (1 - ε) ^ (⌈((N : ℝ) - d * (2 * M + 1)) / (M + 1)⌉₊ - i) <
      ℙ.real {ω | 1 - ε ≤
        P.real {ξ | ξ.2 ∈ I (sol (A fun t => x t ω) fun t => x t ω) ξ.1}} := by -- --- PROOF ---
  haveI : IsProbabilityMeasure P := hP ▸ Measure.isProbabilityMeasure_map (hx 0).aemeasurable
  set W := ⌈((N : ℝ) - d * (2 * M + 1)) / (M + 1)⌉₊ with hW
  set g : ℝ → ℝ := fun p => ∑ i ∈ Finset.range (k + 1),
    (W.choose i : ℝ) * p ^ i * (1 - p) ^ (W - i) with hg
  set G := {ω | 1 - ε ≤
    P.real {ξ | ξ.2 ∈ I (sol (A fun t => x t ω) fun t => x t ω) ξ.1}} with hG
  set C := {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1} with hC
  have hR : ∀ Q, P.real (Prod.mk Q ⁻¹' Cᶜ) = 1 - P.real {ξ : Φ × Y | ξ.2 ∈ I Q ξ.1} := fun Q =>
    probReal_compl_eq_one_sub (measurable_prodMk_left hIm)
  have hGm : 0 ≤ ℙ.real G := measureReal_nonneg
  by_cases hkW : k < W
  swap
  · -- `W ≤ k`: the tail is `1`, so `β = C(N, d)`
    rw [show (∑ i ∈ Finset.range (k + 1), (W.choose i : ℝ) * ε ^ i * (1 - ε) ^ (W - i)) = 1 from
      aux_binom_sum_eq_one (by omega) ε, mul_one]
    rcases Nat.lt_or_ge d 1 with hd0 | hd1
    swap
    · have := aux_two_le_choose hd1 (show d < N by omega)
      have : (2 : ℝ) ≤ N.choose d := by exact_mod_cast this
      linarith
    -- `d = 0`: the solution is consistent with every observation
    obtain rfl : d = 0 := by omega
    have hsol0 : ∀ X X', sol ∅ X = sol ∅ X' := fun X X' =>
      ipm_sol_congr (fun X => hsol ∅ X (by simp)) (by simp)
    -- every problem has the solution without constraints
    have hall : ∀ X F, sol F X = sol ∅ X := fun X F => by
      obtain ⟨H, -, hHc, hHs⟩ := ipm_exists_subset_card_eq hμ hI hd hsol X F (Nat.zero_le _)
      rw [← hHs, Finset.card_eq_zero.mp hHc]
    have hcons : ∀ X ξ, ξ ∈ {ξ : Φ × Y | ξ.2 ∈ I (sol ∅ X) ξ.1} := fun X ξ => by
      have h0 : 0 < N := by omega
      have := (hsol {⟨0, h0⟩} (fun _ => ξ) (Nat.zero_le _)).2.1 ⟨0, h0⟩
        (Finset.mem_singleton_self _)
      rw [hall, hsol0 _ X] at this
      exact this
    have hGu : G = Set.univ := by
      ext ω
      simp only [hG, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have : {ξ : Φ × Y | ξ.2 ∈ I (sol (A fun t => x t ω) fun t => x t ω) ξ.1} = Set.univ := by
        ext ξ; simp only [Set.mem_univ, iff_true]; rw [hall]; exact hcons _ ξ
      rw [this, probReal_univ]
      linarith
    rw [hGu, probReal_univ]
    simp
  -- the marginals are `P`
  have hmarg : ∀ t, ℙ.map (x t) = P := by
    intro t
    have hm : ∀ s, Measurable fun ω (i : Fin 1) => x (i + s) ω :=
      fun s => measurable_pi_lambda _ fun i => hx _
    have e1 : x t = (fun f : Fin 1 → Φ × Y => f 0) ∘ fun ω (i : Fin 1) => x (i + t) ω := by
      funext ω; simp
    have e0 : x 0 = (fun f : Fin 1 → Φ × Y => f 0) ∘ fun ω (i : Fin 1) => x i ω := by
      funext ω; simp
    rw [e1, ← Measure.map_map (measurable_pi_apply 0) (hm t), hstat 1 t,
      Measure.map_map (measurable_pi_apply 0) (by simpa using hm 0), ← e0, hP]
  -- the event of a bad solution of `d` constraints `H` violating at most `k` of the others
  let EH : Finset (Fin N) → Set Ω := fun H =>
    {ω | ε < P.real (Prod.mk (sol H fun t => x t ω) ⁻¹' Cᶜ) ∧
      (Finset.univ.filter fun t => t ∉ H ∧ x t ω ∈ Prod.mk (sol H fun t => x t ω) ⁻¹' Cᶜ).card
        ≤ k}
  have hcover : Gᶜ ⊆ ⋃ H ∈ Finset.univ.powersetCard d, EH H := by
    intro ω hω
    simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    obtain ⟨H, hHA, hHc, hHs⟩ := ipm_exists_subset_card_eq hμ hI hd hsol (fun t => x t ω)
      (A fun t => x t ω) (by rw [hA]; omega)
    refine Set.mem_biUnion (x := H) (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hHc⟩) ?_
    refine ⟨by rw [hHs, hR]; linarith, ?_⟩
    -- the violated constraints were discarded
    have hsub : (Finset.univ.filter fun t => t ∉ H ∧
        x t ω ∈ Prod.mk (sol H fun t => x t ω) ⁻¹' Cᶜ) ⊆ (A fun t => x t ω)ᶜ := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_compl_iff,
        hC, Set.mem_setOf_eq, hHs] at ht
      exact Finset.mem_compl.mpr fun htA =>
        ht.2 ((hsol (A fun t => x t ω) (fun t => x t ω) (by rw [hA]; omega)).2.1 t htA)
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, hA, Fintype.card_fin] at this
    omega
  -- each such event has probability below the binomial tail at `ε`
  have hEH : ∀ H ∈ Finset.univ.powersetCard d, ℙ (EH H) < ENNReal.ofReal (g ε) := by
    intro H hH
    rw [Finset.mem_powersetCard] at hH
    obtain ⟨J, hJc, hJ⟩ := exists_separated_card_eq N M H
    rw [hH.2] at hJc
    obtain ⟨ξ₀⟩ := nonempty_of_isProbabilityMeasure P
    let ext : (H → Φ × Y) → Fin N → Φ × Y := fun a t => if h : t ∈ H then a ⟨t, h⟩ else ξ₀
    have hext : Measurable ext := measurable_pi_lambda _ fun t => by
      by_cases h : t ∈ H
      · simpa [ext, h] using measurable_pi_apply (⟨t, h⟩ : H)
      · simp [ext, h]
    let θ : (H → Φ × Y) → E := fun a => sol H (ext a)
    have hθ : Measurable θ := (hsolm H hH.2).comp hext
    let ZH : Ω → H → Φ × Y := fun ω h => x h.1.1 ω
    have hZ : Measurable ZH := measurable_pi_lambda _ fun h => hx _
    haveI : IsProbabilityMeasure (ℙ.map ZH) := Measure.isProbabilityMeasure_map hZ.aemeasurable
    -- the kept points: each independent of all the others kept
    let S : J → Finset ℕ := fun j => ((H ∪ J).erase j.1).image Fin.val
    have hmemS : ∀ (j : J) (t : Fin N), t ∈ H ∪ J → t ≠ j.1 → t.val ∈ S j := fun j t ht hne =>
      Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hne, ht⟩, rfl⟩
    have hHJ : ∀ (j : J) (h : Fin N), h ∈ H → h ≠ j.1 := fun j h hh hhj => by
      rcases (hJ j.1 j.2).1 h hh with h' | h' <;> rw [hhj] at h' <;> omega
    -- each kept point is independent of the values at the others and at `H`
    have hind : ∀ j : J, Indep (MeasurableSpace.comap (x j.1.1) inferInstance)
        (MeasurableSpace.comap (fun ω (s : S j) => x s ω) inferInstance) ℙ := by
      intro j
      refine indep_point_of_mDependent hx hM j.1.1 (S j) fun s hs => ?_
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨hne, ht⟩ := Finset.mem_erase.mp ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (hJ j.1 j.2).1 t ht
      · exact (hJ j.1 j.2).2 t ht hne
    have hlaw := map_prod_pi_eq_of_indep P hZ (y := fun (j : J) => x j.1.1) (fun j => hx _)
      (fun j => hmarg _) (fun j => MeasurableSpace.comap (fun ω (s : S j) => x s ω) inferInstance)
      (fun j => Measurable.of_comap_le (aux_comap_pi_le _ fun h =>
        aux_comap_le_values x (S j) (hmemS j h.1 (Finset.mem_union_left _ h.2) (hHJ j h.1 h.2))))
      (fun j j' hne => Measurable.of_comap_le (aux_comap_le_values x (S j)
        (hmemS j j'.1 (Finset.mem_union_right _ j'.2) fun h => hne (Subtype.ext h))))
      hind
    -- the event lies in `T`, read through the data at `H` and at `J`
    let T := {q : (H → Φ × Y) × (J → Φ × Y) | ε < P.real (Prod.mk (θ q.1) ⁻¹' Cᶜ) ∧
      (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k}
    have hsub : EH H ⊆ (fun ω => (ZH ω, fun j : J => x j.1.1 ω)) ⁻¹' T := by
      intro ω hω
      have hθx : θ (ZH ω) = sol H fun t => x t ω :=
        ipm_sol_congr (fun X => hsol H X (by omega)) fun t ht => by simp [ext, ZH, ht]
      refine ⟨by simpa [hθx] using hω.1, ?_⟩
      refine (Finset.card_le_card_of_injOn (fun j : J => j.1) ?_
        Subtype.val_injective.injOn).trans hω.2
      intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
      exact ⟨fun h => hHJ j j.1 h rfl, by simpa [hθx] using hj⟩
    -- the bound for `W` samples beside the data at `H`
    have hcard : Fintype.card J = W := by rw [Fintype.card_coe, hJc]
    have := measure_prod_violation_lt (ℙ.map ZH) P hIm hθ (ι := J) (by rw [hcard]; exact hkW)
      hε hε1
    rw [hcard] at this
    calc ℙ (EH H) ≤ ℙ ((fun ω => (ZH ω, fun j : J => x j.1.1 ω)) ⁻¹' T) := measure_mono hsub
      _ ≤ ℙ.map (fun ω => (ZH ω, fun j : J => x j.1.1 ω)) T :=
        Measure.le_map_apply (hZ.prodMk (measurable_pi_lambda _ fun j => hx _)).aemeasurable T
      _ = ((ℙ.map ZH).prod (Measure.pi fun _ : J => P)) T := by rw [hlaw]
      _ < ENNReal.ofReal (g ε) := this
  -- the union over the `C(N, d)` choices of `H`
  have hbad : ℙ Gᶜ < ENNReal.ofReal (N.choose d * g ε) := by
    calc ℙ Gᶜ ≤ ℙ (⋃ H ∈ Finset.univ.powersetCard d, EH H) := measure_mono hcover
      _ ≤ ∑ H ∈ Finset.univ.powersetCard d, ℙ (EH H) := measure_biUnion_finset_le _ _
      _ < ∑ H ∈ Finset.univ.powersetCard d, ENNReal.ofReal (g ε) :=
        ENNReal.sum_lt_sum_of_nonempty
          (Finset.powersetCard_nonempty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; omega))
          hEH
      _ = ENNReal.ofReal (N.choose d * g ε) := by
        have hg0 : 0 ≤ g ε := Finset.sum_nonneg fun i _ => by
          have : 0 ≤ 1 - ε := by linarith
          positivity
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  -- the good event and the bad one cover every outcome
  have hcov : (1 : ENNReal) ≤ ℙ G + ℙ Gᶜ := by
    rw [← measure_univ (μ := ℙ), ← Set.union_compl_self G]
    exact measure_union_le _ _
  have hcovR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
    measure_ne_top _ _⟩) hcov
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at hcovR
  have hbadR := ENNReal.toReal_lt_of_lt_ofReal hbad
  simp only [Measure.real] at hbadR hcovR ⊢
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
