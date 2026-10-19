module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Dynamics.Ergodic.AddCircle
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-!
# Pairwise independence at lags above `M` is not enough for [1, Thm. 4]

[1, Thm. 4] bounds the reliability for an `M`-dependent sequence [1, Def. 5], defined there as
`x(t)` and `x(t + s)` independent whenever `|s| > M`: independence of pairs. The proof idea,
"concentrate on data that are `M` instants apart", needs those data independent jointly, which
pairs do not give. On the circle `ℝ/ℤ`, `x(t) = U + tV` with `U, V` independent and uniform is
strictly stationary with uniform marginals, and `x(t)`, `x(t + s)`, `s ≥ 1`, are independent
(`(u, v) ↦ (u + tv, u + (t + s)v)` preserves the measure); so it is `0`-dependent in the printed
sense, with `W = N - d`. With `y = x(t)` read in `(0, 1]`, the interval model `I_Q = (-∞, Q]`
(`d = 1`, cost `Q`, solution `max_t y(t)`), `N = 4`, `k = 0` and `1 - ε = a = 1/128`, the theorem
claims `Prob{max_t y(t) ≥ a} > 1 - 4a³`. But `U ≤ a/2`, `V ≤ a/8` puts all four below `7a/8`, with
probability `a²/16 > 4a³`. The supplied measurability hypotheses of `ipm_reliability` hold too.
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

open MeasureTheory ProbabilityTheory


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the circle read in `(0, 1]`. -/
noncomputable def aux_rep (y : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 0 y : ℝ)

theorem aux_rep_measurable : Measurable aux_rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable

theorem aux_rep_coe {r : ℝ} (hr : r ∈ Set.Ioc 0 1) : aux_rep r = r :=
  AddCircle.equivIoc_coe_of_mem (by simpa using hr)

theorem aux_rep_pos (y : UnitAddCircle) : 0 < aux_rep y := by
  have := (AddCircle.equivIoc 1 0 y).2; exact this.1

-- the reading is additive while the sum stays in `(0, 1]`
theorem aux_rep_add_nsmul (u v : UnitAddCircle) (t : ℕ) (h : aux_rep u + t * aux_rep v ≤ 1) :
    aux_rep (u + t • v) = aux_rep u + t * aux_rep v := by -- --- PROOF ---
  have hu : ((aux_rep u : ℝ) : UnitAddCircle) = u := AddCircle.coe_equivIoc
  have hv : ((aux_rep v : ℝ) : UnitAddCircle) = v := AddCircle.coe_equivIoc
  have hs : u + t • v = ((aux_rep u + t * aux_rep v : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, ← nsmul_eq_mul, AddCircle.coe_nsmul, hu, hv]
  rw [hs]
  exact aux_rep_coe ⟨by have := aux_rep_pos u; have := aux_rep_pos v; positivity, h⟩

-- the reading is uniform: `{y : rep y ≤ c}` has measure `c`
theorem aux_volume_rep_le {c : ℝ} (h1 : c ≤ 1) :
    volume {y : UnitAddCircle | aux_rep y ≤ c} = ENNReal.ofReal c := by -- --- PROOF ---
  rw [AddCircle.add_projection_respects_measure 1 0
    (measurableSet_le aux_rep_measurable measurable_const)]
  have : (QuotientAddGroup.mk ⁻¹' {y : UnitAddCircle | aux_rep y ≤ c} ∩ Set.Ioc 0 (0 + 1) :
      Set ℝ) = Set.Ioc 0 c := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc, zero_add]
    constructor
    · rintro ⟨h, h0r, hr1⟩
      have hr : aux_rep r = r := aux_rep_coe ⟨h0r, hr1⟩
      exact ⟨h0r, by rw [← hr]; exact h⟩
    · rintro ⟨h0r, hrc⟩
      exact ⟨by rw [aux_rep_coe ⟨h0r, hrc.trans h1⟩]; exact hrc, h0r, hrc.trans h1⟩
  rw [this, Real.volume_Ioc, sub_zero]

-- `v ↦ s v` preserves the measure for `s ≥ 1`
theorem aux_map_nsmul {s : ℕ} (hs : 1 ≤ s) :
    Measure.map (fun v : UnitAddCircle => s • v) volume = volume := by
  rcases Nat.lt_or_ge 1 s with h | h
  · exact (AddCircle.ergodic_nsmul h).toMeasurePreserving.map_eq
  · obtain rfl : s = 1 := by omega
    simp

-- the shear `(u, v) ↦ (u + s v, v)` preserves the measure
theorem aux_shear (s : ℕ) :
    MeasurePreserving (fun ω : UnitAddCircle × UnitAddCircle => (ω.1 + s • ω.2, ω.2))
      volume volume := by -- --- PROOF ---
  have h := (MeasurePreserving.id (volume : Measure UnitAddCircle)).skew_product
    (g := fun v u => s • v + u) (by fun_prop)
    (ae_of_all _ fun v => map_add_left_eq_self (volume : Measure UnitAddCircle) (s • v))
  have h2 := (Measure.measurePreserving_swap.comp h).comp Measure.measurePreserving_swap
  have heq : (fun ω : UnitAddCircle × UnitAddCircle => (ω.1 + s • ω.2, ω.2)) =
      (Prod.swap ∘ fun p : UnitAddCircle × UnitAddCircle => (id p.1, s • p.1 + p.2)) ∘
        Prod.swap := by
    funext ω; simp [add_comm]
  rw [heq]
  exact h2

-- and so does `(u, v) ↦ (u, u + s v)` for `s ≥ 1`
theorem aux_shear' {s : ℕ} (hs : 1 ≤ s) :
    MeasurePreserving (fun ω : UnitAddCircle × UnitAddCircle => (ω.1, ω.1 + s • ω.2))
      volume volume := by -- --- PROOF ---
  refine (MeasurePreserving.id (volume : Measure UnitAddCircle)).skew_product
    (g := fun u v => u + s • v) (by fun_prop) (ae_of_all _ fun u => ?_)
  show Measure.map ((fun w => u + w) ∘ fun v : UnitAddCircle => s • v) volume = volume
  rw [← Measure.map_map (measurable_const_add u) (by fun_prop), aux_map_nsmul hs,
    map_add_left_eq_self]

-- `U + tV` and `U + (t + s)V` are independent
theorem aux_indep (t : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    IndepFun (fun ω : UnitAddCircle × UnitAddCircle => ω.1 + t • ω.2)
      (fun ω => ω.1 + (t + s) • ω.2) volume := by -- --- PROOF ---
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  -- both marginals and the pair are images of the measure under preserving maps
  have hpair : (fun ω : UnitAddCircle × UnitAddCircle => (ω.1 + t • ω.2, ω.1 + (t + s) • ω.2)) =
      (fun ω => (ω.1, ω.1 + s • ω.2)) ∘ fun ω => (ω.1 + t • ω.2, ω.2) := by
    funext ω; simp [add_nsmul, add_assoc]
  have hfst : Measure.map Prod.fst (volume : Measure (UnitAddCircle × UnitAddCircle)) = volume :=
    (measurePreserving_fst (μ := volume) (ν := volume)).map_eq
  have e1 : Measure.map (fun ω : UnitAddCircle × UnitAddCircle =>
      (ω.1 + t • ω.2, ω.1 + (t + s) • ω.2)) volume = volume := by
    rw [hpair, ← Measure.map_map (aux_shear' hs).measurable (aux_shear t).measurable,
      (aux_shear t).map_eq, (aux_shear' hs).map_eq]
  have e2 : ∀ r : ℕ, Measure.map (fun ω : UnitAddCircle × UnitAddCircle => ω.1 + r • ω.2) volume =
      volume := fun r => by
    rw [show (fun ω : UnitAddCircle × UnitAddCircle => ω.1 + r • ω.2) =
      Prod.fst ∘ (fun ω => (ω.1 + r • ω.2, ω.2)) from rfl,
      ← Measure.map_map measurable_fst (aux_shear r).measurable, (aux_shear r).map_eq, hfst]
  rw [e1, e2, e2]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipmReliabilityMDependent_counterexample : -- --- CONCL ---
    ¬ ∀ (E Φ Y Ω : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [MeasurableSpace Φ] [MeasurableSpace Y] [MeasurableSpace Ω]
      (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (x : ℕ → Ω → Φ × Y) (P : Measure (Φ × Y))
      (M N d k : ℕ) (𝒬 : Set E) (μQ : E → ℝ) (I : E → Φ → Set Y)
      (sol : Finset (Fin N) → (Fin N → Φ × Y) → E) (A : (Fin N → Φ × Y) → Finset (Fin N))
      (ε : ℝ), (∀ t, Measurable (x t)) →
      -- Assumption 1: strictly stationary, with marginal `P`
      (∀ n s, ℙ.map (fun ω (i : Fin n) => x (i + s) ω) = ℙ.map (fun ω (i : Fin n) => x i ω)) →
      ℙ.map (x 0) = P →
      -- Def. 5: `x(t)` and `x(t + s)` independent for `s > M`
      (∀ t s, M < s → IndepFun (x t) (x (t + s)) ℙ) →
      Module.finrank ℝ E = d → k < N - d → ConvexOn ℝ 𝒬 μQ →
      (∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ}) →
      (∀ F X, d ≤ F.card → sol F X ∈ 𝒬 ∧ (∀ t ∈ F, (X t).2 ∈ I (sol F X) (X t).1) ∧
        ∀ Q ∈ 𝒬, (∀ t ∈ F, (X t).2 ∈ I Q (X t).1) → Q ≠ sol F X → μQ (sol F X) < μQ Q) →
      (∀ X, (A X).card = N - k) →
      MeasurableSet {p : E × (Φ × Y) | p.2.2 ∈ I p.1 p.2.1} →
      (∀ H : Finset (Fin N), H.card = d → Measurable (sol H)) → 0 < ε → ε < 1 →
      1 - (N.choose d : ℝ) * ∑ i ∈ Finset.range (k + 1),
          ((⌈((N : ℝ) - d * (2 * M + 1)) / (M + 1)⌉₊).choose i : ℝ) * ε ^ i *
            (1 - ε) ^ (⌈((N : ℝ) - d * (2 * M + 1)) / (M + 1)⌉₊ - i) <
        ℙ.real {ω | 1 - ε ≤
          P.real {ξ | ξ.2 ∈ I (sol (A fun t => x t ω) fun t => x t ω) ξ.1}} := by -- --- PROOF ---
  intro h
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  set a : ℝ := 1 / 128 with ha
  let x : ℕ → UnitAddCircle × UnitAddCircle → Unit × UnitAddCircle := fun t ω =>
    ((), ω.1 + t • ω.2)
  let I : ℝ → Unit → Set UnitAddCircle := fun Q _ => {y | aux_rep y ≤ Q}
  let sol : Finset (Fin 4) → (Fin 4 → Unit × UnitAddCircle) → ℝ := fun F X =>
    if hF : F.Nonempty then F.sup' hF fun t => aux_rep (X t).2 else 0
  have hx : ∀ t, Measurable (x t) := fun t => measurable_const.prodMk (by fun_prop)
  -- Assumption 1: a shift of the sequence is the shear
  have hstat : ∀ n s, (volume : Measure (UnitAddCircle × UnitAddCircle)).map
      (fun ω (i : Fin n) => x (i + s) ω) = volume.map (fun ω (i : Fin n) => x i ω) := by
    intro n s
    have hm : Measurable fun ω (i : Fin n) => x i ω := measurable_pi_lambda _ fun i => hx i
    have : (fun ω (i : Fin n) => x (i + s) ω) =
        (fun ω (i : Fin n) => x i ω) ∘ fun ω => (ω.1 + s • ω.2, ω.2) := by
      funext ω i; simp only [x, Function.comp_apply, add_nsmul]; abel_nf
    rw [this, ← Measure.map_map hm (aux_shear s).measurable, (aux_shear s).map_eq]
  -- Def. 5 with `M = 0`
  have hind : ∀ t s, 0 < s → IndepFun (x t) (x (t + s)) volume := fun t s hs =>
    (aux_indep t hs).comp (measurable_const.prodMk measurable_id)
      (measurable_const.prodMk measurable_id)
  -- the problem: convex, solved by the largest sample, measurable
  have hconv : ∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ} := fun _ y => convex_Ici (aux_rep y)
  have hsol : ∀ F X, 1 ≤ F.card → sol F X ∈ Set.univ ∧ (∀ t ∈ F, (X t).2 ∈ I (sol F X) (X t).1) ∧
      ∀ Q ∈ Set.univ, (∀ t ∈ F, (X t).2 ∈ I Q (X t).1) → Q ≠ sol F X → id (sol F X) < id Q := by
    intro F X hF
    have hne : F.Nonempty := Finset.card_pos.mp hF
    have hs : sol F X = F.sup' hne fun t => aux_rep (X t).2 := dif_pos hne
    refine ⟨trivial, fun t ht => ?_, fun Q _ hQ hne' => ?_⟩
    · rw [hs]; exact Finset.le_sup' (fun t => aux_rep (X t).2) ht
    · have : sol F X ≤ Q := by rw [hs]; exact Finset.sup'_le hne _ hQ
      exact lt_of_le_of_ne this (Ne.symm hne')
  have hIm : MeasurableSet {p : ℝ × (Unit × UnitAddCircle) | p.2.2 ∈ I p.1 p.2.1} :=
    measurableSet_le (aux_rep_measurable.comp (measurable_snd.comp measurable_snd)) measurable_fst
  have hsolm : ∀ H : Finset (Fin 4), H.card = 1 → Measurable (sol H) := by
    intro H hH
    obtain ⟨t0, rfl⟩ := Finset.card_eq_one.mp hH
    have : sol {t0} = fun X => aux_rep (X t0).2 := by funext X; simp [sol]
    rw [this]; exact aux_rep_measurable.comp (measurable_snd.comp (measurable_pi_apply t0))
  -- the printed theorem at this instance
  have key := h ℝ Unit UnitAddCircle (UnitAddCircle × UnitAddCircle) volume x (volume.map (x 0))
    0 4 1 0 Set.univ id I sol (fun _ => Finset.univ) (1 - a) hx hstat rfl hind
    (Module.finrank_self ℝ) (by norm_num) (convexOn_id convex_univ) hconv hsol (fun _ => by simp)
    hIm hsolm (by norm_num [ha]) (by norm_num [ha])
  -- `W = 3` and `β = 4a³`
  have hW : ⌈(((4 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) * (2 * ((0 : ℕ) : ℝ) + 1)) /
      (((0 : ℕ) : ℝ) + 1)⌉₊ = 3 := by norm_num
  rw [hW] at key
  norm_num at key
  -- the marginal reads the circle uniformly
  have hP : ∀ c, 0 ≤ c → c ≤ 1 →
      (volume.map (x 0)).real {ξ : Unit × UnitAddCircle | aux_rep ξ.2 ≤ c} = c := by
    intro c h0 h1
    rw [Measure.real, Measure.map_apply (hx 0) (show MeasurableSet
      {ξ : Unit × UnitAddCircle | aux_rep ξ.2 ≤ c} from
        measurableSet_le (aux_rep_measurable.comp measurable_snd) measurable_const)]
    have : x 0 ⁻¹' {ξ : Unit × UnitAddCircle | aux_rep ξ.2 ≤ c} =
        {u | aux_rep u ≤ c} ×ˢ Set.univ := by
      ext ω; simp [x]
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, aux_volume_rep_le h1, measure_univ,
      mul_one, ENNReal.toReal_ofReal h0]
  set G := {ω : UnitAddCircle × UnitAddCircle | (1 : ℝ) / 128 ≤ (volume.map (x 0)).real
    {ξ | ξ.2 ∈ I (sol Finset.univ fun t => x t ω) ξ.1}} with hG
  set B := {u : UnitAddCircle | aux_rep u ≤ a / 2} ×ˢ {v : UnitAddCircle | aux_rep v ≤ a / 8}
  have hBm : MeasurableSet B := (measurableSet_le aux_rep_measurable measurable_const).prod
    (measurableSet_le aux_rep_measurable measurable_const)
  -- `U ≤ a/2`, `V ≤ a/8` keep all four samples below `7a/8`: a bad outcome
  have hdisj : Disjoint G B := by
    rw [Set.disjoint_left]
    intro ω hωG hωB
    obtain ⟨hu, hv⟩ := hωB
    -- each sample is `U + tV` read without wrapping
    have hu' : aux_rep ω.1 ≤ a / 2 := hu
    have hv' : aux_rep ω.2 ≤ a / 8 := hv
    have hyt : ∀ t : Fin 4, aux_rep (ω.1 + (t : ℕ) • ω.2) ≤ 7 * a / 8 := by
      intro t
      have ht : ((t : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp t.2
      have hv0 := (aux_rep_pos ω.2).le
      rw [aux_rep_add_nsmul _ _ _ (by nlinarith)]
      nlinarith
    have hs : sol Finset.univ (fun t => x t ω) ≤ 7 * a / 8 := by
      simp only [sol, dif_pos Finset.univ_nonempty]
      exact Finset.sup'_le _ _ fun t _ => hyt t
    have hle : (volume.map (x 0)).real {ξ : Unit × UnitAddCircle |
        ξ.2 ∈ I (sol Finset.univ fun t => x t ω) ξ.1} ≤
        (volume.map (x 0)).real {ξ : Unit × UnitAddCircle | aux_rep ξ.2 ≤ 7 * a / 8} :=
      measureReal_mono fun ξ hξ => le_trans hξ hs
    rw [hP _ (by positivity) (by norm_num [ha])] at hle
    have : (1 : ℝ) / 128 ≤ _ := hωG
    linarith
  -- so the good outcomes have probability at most `1 - a²/16`
  have hBv : volume B = ENNReal.ofReal (a / 2) * ENNReal.ofReal (a / 8) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, aux_volume_rep_le (by norm_num [ha]),
      aux_volume_rep_le (by norm_num [ha])]
  have hle1 : volume (G ∪ B) ≤ 1 := prob_le_one
  rw [measure_union hdisj hBm] at hle1
  have hR := ENNReal.toReal_mono ENNReal.one_ne_top hle1
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hBv, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_one] at hR
  simp only [Measure.real] at key
  norm_num [ha] at hR
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
