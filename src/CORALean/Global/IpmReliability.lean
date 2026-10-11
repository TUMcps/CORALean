import CORALean.Global.SupportConstraintsLengthLe
import CORALean.Global.BinomialTailStrictAntiOn
import CORALean.Global.PiCountLeMeasureLe
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The reliability of an identified interval predictor model

[1, Thm. 3]: data `x(t) = (ϕ(t), y(t))`, `t = 1, …, N`, independent with marginal `P` (Assumptions
1-2), a convex Problem 1′ in `d` variables `Q ∈ 𝒬` with cost `μ_Q` and constraints
`y(t) ∈ I_Q(ϕ(t))`, `t ∈ A(D_N)`, kept by any algorithm `A` discarding `k < N - d` of them, and
`ε ∈ (0, 1)`: the solution `Î^A_{N,k}` has reliability `R = P{y ∈ I(ϕ)} ≥ 1 - ε` with probability
`> 1 - β`, `β = β₀ Σ_{i=0}^k C(N - d, i) εⁱ/(1 - ε)ⁱ` (Eq. 13), `β₀ = C(N, d)(1 - ε)^{N-d}`
(Eq. 14). The proof is Appendix B: `d` of the kept constraints give the same solution
(`supportConstraints_length_le`), which violates at most `k` of the other `N - d` samples; given
the `d`, that has probability `Σ_{i≤k} C(N-d, i) ζⁱ(1-ζ)^{N-d-i}` (`measure_pi_card_filter_le`),
below its value at `ε` when `ζ > ε` (`binomialTail_strictAntiOn`); a union over the `C(N, d)` sets.
The solutions `ẑ_F` are assumed unique for every `F` of at least `d` constraints, as the proof
uses them. Not printed and supplied: the consistency relation `y ∈ I_Q(ϕ)` is jointly measurable
and the solution map from `d` constraints is measurable, without which the probabilities in the
proof are not defined. Where no bad outcome has positive probability the printed chain's first
strict inequality reads `0 < 0`; the bound stays strict through the second.
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {E Φ Y : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {N d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `ẑ_F`, from at least `d` constraints, is the unique minimizer of the cost over them
abbrev aux_IsUniqueSol (𝒬 : Set E) (μQ : E → ℝ) (I : E → Φ → Set Y) (d : ℕ)
    (sol : Finset (Fin N) → (Fin N → Φ × Y) → E) : Prop :=
  ∀ F x, d ≤ F.card → sol F x ∈ 𝒬 ∧ (∀ t ∈ F, (x t).2 ∈ I (sol F x) (x t).1) ∧
    ∀ Q ∈ 𝒬, (∀ t ∈ F, (x t).2 ∈ I Q (x t).1) → Q ≠ sol F x → μQ (sol F x) < μQ Q

-- the solution from `H` reads the data at `H` only
omit [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] in
theorem aux_ipm_sol_congr {𝒬 : Set E} {μQ : E → ℝ} {I : E → Φ → Set Y}
    {sol : Finset (Fin N) → (Fin N → Φ × Y) → E} (hsol : aux_IsUniqueSol 𝒬 μQ I d sol)
    {H : Finset (Fin N)} (hH : d ≤ H.card) {x x' : Fin N → Φ × Y} (hxx : ∀ t ∈ H, x t = x' t) :
    sol H x = sol H x' := by -- --- PROOF ---
  by_contra hne
  obtain ⟨h1, h2, h3⟩ := hsol H x hH
  obtain ⟨h1', h2', h3'⟩ := hsol H x' hH
  have a := h3 (sol H x') h1' (fun t ht => hxx t ht ▸ h2' t ht) (Ne.symm hne)
  have b := h3' (sol H x) h1 (fun t ht => (hxx t ht).symm ▸ h2 t ht) hne
  exact lt_asymm a b

-- non-support constraints are removed one at a time until `d` are left, the solution unchanged
theorem aux_ipm_exists_card_eq {𝒬 : Set E} {μQ : E → ℝ} (hμ : ConvexOn ℝ 𝒬 μQ)
    {I : E → Φ → Set Y} (hI : ∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ}) (hd : Module.finrank ℝ E = d)
    {sol : Finset (Fin N) → (Fin N → Φ × Y) → E} (hsol : aux_IsUniqueSol 𝒬 μQ I d sol)
    (x : Fin N → Φ × Y) (n : ℕ) :
    ∀ F : Finset (Fin N), F.card = d + n →
      ∃ H ⊆ F, H.card = d ∧ sol H x = sol F x := by -- --- PROOF ---
  classical
  induction n with
  | zero => intro F hF; exact ⟨F, subset_rfl, by omega, rfl⟩
  | succ n ih =>
    intro F hF
    obtain ⟨hF1, hF2, hF3⟩ := hsol F x (by omega)
    have hlen := supportConstraints_length_le 𝒬 μQ hμ (fun t => {Q | (x t).2 ∈ I Q (x t).1})
      (fun t => hI _ _) (fun G => sol G x) F
      ⟨hF1, hF2, fun z hz hzF => by
        by_cases h : z = sol F x
        · rw [h]
        · exact (hF3 z hz hzF h).le⟩
      fun l hl => by
        obtain ⟨h1, h2, -⟩ := hsol (F.erase l) x (by rw [Finset.card_erase_of_mem hl]; omega)
        exact ⟨h1, h2⟩
    -- some constraint of `F` is not a support constraint, as `|F| > d`
    have hlt : (supportConstraints (fun G => μQ (sol G x)) F).toFinset.card < F.card :=
      (List.toFinset_card_le _).trans_lt (by omega)
    obtain ⟨l, hlF, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hns : ¬ μQ (sol (F.erase l) x) < μQ (sol F x) := fun h =>
      hl (by simp [supportConstraints, hlF, h])
    have hcard : (F.erase l).card = d + n := by rw [Finset.card_erase_of_mem hlF]; omega
    -- the solution without it is the same
    have heq : sol (F.erase l) x = sol F x := by
      by_contra hne
      obtain ⟨-, -, h3⟩ := hsol (F.erase l) x (by omega)
      exact hns (h3 (sol F x) hF1 (fun t ht => hF2 t (Finset.mem_of_mem_erase ht)) (Ne.symm hne))
    obtain ⟨H, hHF, hHc, hHs⟩ := ih (F.erase l) hcard
    exact ⟨H, hHF.trans (Finset.erase_subset _ _), hHc, hHs.trans heq⟩


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
theorem ipm_reliability [MeasurableSpace E] [MeasurableSpace Φ] [MeasurableSpace Y]
    (hd : Module.finrank ℝ E = d) {k : ℕ} (hk : k < N - d) (𝒬 : Set E) (μQ : E → ℝ)
    (hμ : ConvexOn ℝ 𝒬 μQ) (I : E → Φ → Set Y) (hI : ∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ})
    (sol : Finset (Fin N) → (Fin N → Φ × Y) → E)
    (hsol : ∀ F x, d ≤ F.card → sol F x ∈ 𝒬 ∧ (∀ t ∈ F, (x t).2 ∈ I (sol F x) (x t).1) ∧
      ∀ Q ∈ 𝒬, (∀ t ∈ F, (x t).2 ∈ I Q (x t).1) → Q ≠ sol F x → μQ (sol F x) < μQ Q)
    (A : (Fin N → Φ × Y) → Finset (Fin N)) (hA : ∀ x, (A x).card = N - k)
    (P : Measure (Φ × Y)) [IsProbabilityMeasure P]
    (hIm : MeasurableSet {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1})
    (hsolm : ∀ H : Finset (Fin N), H.card = d → Measurable (sol H)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    1 - (N.choose d : ℝ) * (1 - ε) ^ (N - d) *
        ∑ i ∈ Finset.range (k + 1), ((N - d).choose i : ℝ) * ε ^ i / (1 - ε) ^ i <
      (Measure.pi fun _ : Fin N => P).real
        {x | 1 - ε ≤ P.real {ξ | ξ.2 ∈ I (sol (A x) x) ξ.1}} := by -- --- PROOF ---
  set μN := Measure.pi fun _ : Fin N => P
  set C := {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1} with hC
  set g : ℝ → ℝ := fun p => ∑ i ∈ Finset.range (k + 1),
    ((N - d).choose i : ℝ) * p ^ i * (1 - p) ^ (N - d - i) with hg
  have hanti : StrictAntiOn g (Set.Icc 0 1) := binomialTail_strictAntiOn hk
  have hR : ∀ Q, P.real (Prod.mk Q ⁻¹' Cᶜ) = 1 - P.real {ξ : Φ × Y | ξ.2 ∈ I Q ξ.1} := fun Q =>
    probReal_compl_eq_one_sub (measurable_prodMk_left hIm)
  have hgpos : 0 < g ε := by
    simp only [hg]
    rw [Finset.sum_range_succ']
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => by
      have : 0 ≤ 1 - ε := by linarith
      positivity) ?_
    simpa using pow_pos (by linarith : (0 : ℝ) < 1 - ε) _
  -- the event of a bad solution of `d` constraints `H` violating at most `k` of the others
  let EH : Finset (Fin N) → Set (Fin N → Φ × Y) := fun H =>
    {x | ε < P.real (Prod.mk (sol H x) ⁻¹' Cᶜ) ∧
      (Finset.univ.filter fun t => t ∉ H ∧ x t ∈ Prod.mk (sol H x) ⁻¹' Cᶜ).card ≤ k}
  have hcover : {x | P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1} < 1 - ε} ⊆
      ⋃ H ∈ Finset.univ.powersetCard d, EH H := by
    intro x hx
    obtain ⟨H, hHA, hHc, hHs⟩ := aux_ipm_exists_card_eq hμ hI hd hsol x (N - k - d) (A x)
      (by rw [hA]; omega)
    refine Set.mem_biUnion (x := H) (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hHc⟩) ?_
    refine ⟨by rw [hHs, hR]; simp only [Set.mem_setOf_eq] at hx; linarith, ?_⟩
    -- the violated constraints were discarded
    have hsub : (Finset.univ.filter fun t => t ∉ H ∧ x t ∈ Prod.mk (sol H x) ⁻¹' Cᶜ) ⊆
        (A x)ᶜ := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_compl_iff,
        hC, Set.mem_setOf_eq, hHs] at ht
      exact Finset.mem_compl.mpr fun htA =>
        ht.2 ((hsol (A x) x (by rw [hA]; omega)).2.1 t htA)
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, hA, Fintype.card_fin] at this
    omega
  -- each such event has probability below the binomial tail at `ε`
  have hEH : ∀ H ∈ Finset.univ.powersetCard d, μN (EH H) < ENNReal.ofReal (g ε) := by
    intro H hH
    rw [Finset.mem_powersetCard] at hH
    obtain ⟨ξ₀⟩ := nonempty_of_isProbabilityMeasure P
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Φ × Y) (· ∈ H)
    have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => P) (· ∈ H)
    set μH := Measure.pi fun _ : {t // t ∈ H} => P
    set μHc := Measure.pi fun _ : {t // t ∉ H} => P
    let θ : ({t // t ∈ H} → Φ × Y) → E := fun a => sol H (e.symm (a, fun _ => ξ₀))
    have hθ : Measurable θ :=
      (hsolm H hH.2).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
    let ζ : ({t // t ∈ H} → Φ × Y) → ℝ := fun a => P.real (Prod.mk (θ a) ⁻¹' Cᶜ)
    have hζ : Measurable ζ :=
      ((measurable_measure_prodMk_left hIm.compl).comp hθ).ennreal_toReal
    have hζ1 : ∀ a, ζ a ≤ 1 := fun a => measureReal_le_one
    set S := {a | ε < ζ a}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hζ
    let T := {q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) | ε < ζ q.1 ∧
      (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k}
    -- `T` is measurable: the pattern of violations is a measurable finite-valued map
    have hT : MeasurableSet T := by
      let v : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) → ({t // t ∉ H} → Bool) :=
        fun q j => if q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ then true else false
      have hv : Measurable v := measurable_pi_lambda _ fun j => measurable_to_bool (by
        have : (fun q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) =>
            if q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ then true else false) ⁻¹' {true} =
            (fun q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) => (θ q.1, q.2 j)) ⁻¹' Cᶜ := by
          ext q; simp
        rw [this]
        exact hIm.compl.preimage ((hθ.comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd)))
      have hset : {q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) |
          (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k} =
          v ⁻¹' {w | (Finset.univ.filter fun j => w j = true).card ≤ k} := by
        ext q; simp [v]
      have h2 : MeasurableSet {q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) |
          (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k} := by
        rw [hset]; exact (Set.toFinite _).measurableSet.preimage hv
      exact (measurableSet_lt measurable_const (hζ.comp measurable_fst)).inter h2
    -- the event lies in `T`, read through the split of the data at `H`
    have hsub : EH H ⊆ e ⁻¹' T := by
      intro x hx
      have hθx : θ (fun i => x i) = sol H x := aux_ipm_sol_congr hsol (by omega) fun t ht => by
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, ht]
      refine ⟨by simpa [e, ζ, hθx] using hx.1, ?_⟩
      refine (Finset.card_le_card_of_injOn (fun j => j.1) ?_ Subtype.val_injective.injOn).trans hx.2
      intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
      exact ⟨j.2, by simpa [e, hθx] using hj⟩
    -- given the data at `H`, the rest violate at most `k` with the binomial tail's probability
    have hcard : Fintype.card {t // t ∉ H} = N - d := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hH.2]
    have hsec : ∀ a, μHc (Prod.mk a ⁻¹' T) ≤ S.indicator (fun a => ENNReal.ofReal (g (ζ a))) a := by
      intro a
      by_cases ha : a ∈ S
      · rw [Set.indicator_of_mem ha]
        have hset : Prod.mk a ⁻¹' T =
            {b | (Finset.univ.filter fun j => b j ∈ Prod.mk (θ a) ⁻¹' Cᶜ).card ≤ k} := by
          ext b; simp [T, show ε < ζ a from ha]
        rw [hset]
        have := measure_pi_card_filter_le (ι := {t // t ∉ H}) P
          (measurable_prodMk_left hIm.compl : MeasurableSet (Prod.mk (θ a) ⁻¹' Cᶜ)) k
        rw [hcard] at this
        exact this
      · have hset : Prod.mk a ⁻¹' T = ∅ := by
          ext b; simp [T, show ¬ ε < ζ a from ha]
        simp [hset]
    -- where the solution from `H` is bad, the tail is below its value at `ε`
    have hlt : ∀ a ∈ S, g (ζ a) < g ε := fun a ha =>
      hanti ⟨hε.le, hε1.le⟩ ⟨(hε.trans ha).le, hζ1 a⟩ ha
    have hfin : ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μH ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const fun a ha =>
        ENNReal.ofReal_le_ofReal (hlt a ha).le)
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    -- Fubini over the split of the data at `H`, then strict on a bad set of positive measure
    calc μN (EH H) ≤ μN (e ⁻¹' T) := measure_mono hsub
      _ = (μH.prod μHc) T := by convert hmp.measure_preimage hT.nullMeasurableSet
      _ = ∫⁻ a, μHc (Prod.mk a ⁻¹' T) ∂μH := Measure.prod_apply hT
      _ ≤ ∫⁻ a, S.indicator (fun a => ENNReal.ofReal (g (ζ a))) a ∂μH := lintegral_mono hsec
      _ = ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μH := lintegral_indicator hS _
      _ < ENNReal.ofReal (g ε) := by
        by_cases hS0 : μH S = 0
        · rw [Measure.restrict_eq_zero.mpr hS0, lintegral_zero_measure]
          exact ENNReal.ofReal_pos.mpr hgpos
        calc ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μH < ∫⁻ a in S, ENNReal.ofReal (g ε) ∂μH :=
              setLIntegral_strict_mono hS hS0 measurable_const hfin (ae_of_all _ fun a ha =>
                (ENNReal.ofReal_lt_ofReal_iff hgpos).mpr (hlt a ha))
          _ = ENNReal.ofReal (g ε) * μH S := setLIntegral_const _ _
          _ ≤ ENNReal.ofReal (g ε) * 1 := by gcongr; exact prob_le_one
          _ = ENNReal.ofReal (g ε) := mul_one _
  -- the union over the `C(N, d)` choices of `H`
  have hbad : μN {x | P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1} < 1 - ε} <
      ENNReal.ofReal (N.choose d * g ε) := by
    calc μN {x | P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1} < 1 - ε}
        ≤ μN (⋃ H ∈ Finset.univ.powersetCard d, EH H) := measure_mono hcover
      _ ≤ ∑ H ∈ Finset.univ.powersetCard d, μN (EH H) := measure_biUnion_finset_le _ _
      _ < ∑ H ∈ Finset.univ.powersetCard d, ENNReal.ofReal (g ε) :=
        ENNReal.sum_lt_sum_of_nonempty
          (Finset.powersetCard_nonempty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; omega))
          hEH
      _ = ENNReal.ofReal (N.choose d * g ε) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  -- `β` of Eqs. 13-14 is that union bound
  have hβ : (N.choose d : ℝ) * (1 - ε) ^ (N - d) *
      ∑ i ∈ Finset.range (k + 1), ((N - d).choose i : ℝ) * ε ^ i / (1 - ε) ^ i =
      N.choose d * g ε := by
    simp only [hg, mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ N - d := by simp at hi; omega
    have h1 : (1 - ε) ^ i ≠ 0 := pow_ne_zero _ (by linarith)
    rw [show (1 - ε) ^ (N - d) = (1 - ε) ^ (N - d - i) * (1 - ε) ^ i by
      rw [← pow_add, Nat.sub_add_cancel hik]]
    field_simp
  -- the good event and the bad one cover every outcome
  have hcov : (1 : ENNReal) ≤ μN {x | 1 - ε ≤ P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1}} +
      μN {x | P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1} < 1 - ε} := by
    rw [← measure_univ (μ := μN)]
    refine (measure_mono fun x _ => ?_).trans (measure_union_le _ _)
    exact (le_or_gt (1 - ε) _).elim Or.inl Or.inr
  have hcovR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
    measure_ne_top _ _⟩) hcov
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at hcovR
  have hbadR := ENNReal.toReal_lt_of_lt_ofReal hbad
  rw [hβ]
  simp only [Measure.real] at hbadR hcovR ⊢
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
