module

public import CORALean.Global.IpmExistsSubsetCardEq
public import CORALean.Global.IpmSolCongr
public import CORALean.Global.MeasureProdViolationLt

@[expose] public section

/-!
# The reliability of an identified interval predictor model

[1, Thm. 3]: data `x(t) = (ϕ(t), y(t))`, `t = 1, …, N`, independent with marginal `P`, a convex
Problem 1′ in `d` variables with constraints `y(t) ∈ I_Q(ϕ(t))`, kept by an algorithm `A` discarding
`k < N - d`, and `ε ∈ (0, 1)`: the solution `Î^A_{N,k}` has reliability `R = P{y ∈ I(ϕ)} ≥ 1 - ε`
with probability `> 1 - β`, `β` of Eq. 13-14. Appendix B: `d` of the kept constraints give the same
solution (`ipm_exists_subset_card_eq`), which violates at most `k` of the other samples, with
probability below the binomial tail at `ε` when it is bad (`measure_prod_violation_lt`); a union
bound over the choices of `d`. Uniqueness of the solutions and joint measurability of the
consistency relation are supplied, unstated in the paper.

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {E Φ Y : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {N d : ℕ}


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
    (hε1 : ε < 1) : -- --- CONCL ---
    1 - (N.choose d : ℝ) * (1 - ε) ^ (N - d) *
        ∑ i ∈ Finset.range (k + 1), ((N - d).choose i : ℝ) * ε ^ i / (1 - ε) ^ i <
      (Measure.pi fun _ : Fin N => P).real
        {x | 1 - ε ≤ P.real {ξ | ξ.2 ∈ I (sol (A x) x) ξ.1}} := by -- --- PROOF ---
  set μN := Measure.pi fun _ : Fin N => P
  set C := {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1} with hC
  set g : ℝ → ℝ := fun p => ∑ i ∈ Finset.range (k + 1),
    ((N - d).choose i : ℝ) * p ^ i * (1 - p) ^ (N - d - i) with hg
  have hR : ∀ Q, P.real (Prod.mk Q ⁻¹' Cᶜ) = 1 - P.real {ξ : Φ × Y | ξ.2 ∈ I Q ξ.1} := fun Q =>
    probReal_compl_eq_one_sub (measurable_prodMk_left hIm)
  -- the event of a bad solution of `d` constraints `H` violating at most `k` of the others
  let EH : Finset (Fin N) → Set (Fin N → Φ × Y) := fun H =>
    {x | ε < P.real (Prod.mk (sol H x) ⁻¹' Cᶜ) ∧
      (Finset.univ.filter fun t => t ∉ H ∧ x t ∈ Prod.mk (sol H x) ⁻¹' Cᶜ).card ≤ k}
  have hcover : {x | P.real {ξ : Φ × Y | ξ.2 ∈ I (sol (A x) x) ξ.1} < 1 - ε} ⊆
      ⋃ H ∈ Finset.univ.powersetCard d, EH H := by
    intro x hx
    obtain ⟨H, hHA, hHc, hHs⟩ := ipm_exists_subset_card_eq hμ hI hd hsol x (A x)
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
    let T := {q : ({t // t ∈ H} → Φ × Y) × ({t // t ∉ H} → Φ × Y) |
      ε < P.real (Prod.mk (θ q.1) ⁻¹' Cᶜ) ∧
        (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k}
    -- the event lies in `T`, read through the split of the data at `H`
    have hsub : EH H ⊆ e ⁻¹' T := by
      intro x hx
      have hθx : θ (fun i => x i) = sol H x :=
        ipm_sol_congr (fun x => hsol H x (by omega)) fun t ht => by
          simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, ht]
      refine ⟨by simpa [e, hθx] using hx.1, ?_⟩
      refine (Finset.card_le_card_of_injOn (fun j => j.1) ?_ Subtype.val_injective.injOn).trans hx.2
      intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
      exact ⟨j.2, by simpa [e, hθx] using hj⟩
    -- the other `N - d` points are independent of the data at `H`
    have hcard : Fintype.card {t // t ∉ H} = N - d := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hH.2]
    have := measure_prod_violation_lt μH P hIm hθ (ι := {t // t ∉ H})
      (by rw [hcard]; exact hk) hε hε1
    rw [hcard] at this
    calc μN (EH H) ≤ μN (e ⁻¹' T) := measure_mono hsub
      _ ≤ μN.map e T := Measure.le_map_apply e.measurable.aemeasurable T
      _ = (μH.prod μHc) T := by rw [hmp.map_eq]; convert rfl
      _ < ENNReal.ofReal (g ε) := this
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
