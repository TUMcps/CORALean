import CORALean.NN.Layers.ActivationPolyInflate
import CORALean.NN.Layers.PolyRangeConvergence
import CORALean.NN.Operations.RefinementConvergent

/-!
# The activation layer as a refinable layer

The refinement loop's one interesting layer [1]. A `PolyRelaxationFamily` is a
relaxation per level, the order free to grow with it, and the layer reads the
level as nothing but an index into that family — every level is sound, so the
schedule decides precision alone.

`polyRelaxationFamily` is the family a loop actually runs: level `o` fits `σ` on
`[-o, o]` to within `1 / (o + 1)`, so a level widens the range and tightens the
fit at once. Both are needed, and the range is the reason: a polynomial is
unbounded, so no single fit can serve every input set, and a level has to say
where it is accurate as well as how accurately.

It is built by choice, `exists_polyRelaxation_error_lt` being an existence
statement — CORA's `poly_method` is one of the many witnesses, and which one is
picked is a precision question that `sound` already answers for.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise ContSet

variable {σ σ' : ℝ → ℝ} {Mσ : ℝ} {n : ℕ}

/-- A polynomial relaxation per refinement level, the order free to grow. -/
structure PolyRelaxationFamily (σ : ℝ → ℝ) where
  deg : ℕ → ℕ
  rel : (o : ℕ) → PolyRelaxation σ (deg o)

/-- The activation layer of a family: one `σ`, one enclosure per level. -/
noncomputable def Layer.activationPolyRefinable (F : PolyRelaxationFamily σ) :
    RefinableLayer 𝒫𝒵 n n where
  eval x := fun i => σ (x i)
  propagate o := (Layer.activationPoly (F.rel o)).propagate
  propagate_outer o := (Layer.activationPoly (F.rel o)).propagate_outer

/-- What level `o` is asked for, named once so the family and its bound agree. -/
theorem aux_exists_polyRelaxation_at_level (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) (o : ℕ) :
    ∃ (k : ℕ) (P : PolyRelaxation σ k), ∀ l u : ℝ,
      -(o : ℝ) ≤ l → l ≤ u → u ≤ (o : ℝ) → P.error l u < 1 / ((o : ℝ) + 1) :=
  exists_polyRelaxation_error_lt hd hσ (by positivity)

/-- Level `o` fits `σ` on `[-o, o]` to within `1 / (o + 1)`. -/
noncomputable def polyRelaxationFamily (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) : PolyRelaxationFamily σ where
  deg o := (aux_exists_polyRelaxation_at_level hd hσ o).choose
  rel o := (aux_exists_polyRelaxation_at_level hd hσ o).choose_spec.choose

theorem polyRelaxationFamily_error_lt (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) (o : ℕ) {l u : ℝ}
    (hl : -(o : ℝ) ≤ l) (hlu : l ≤ u) (hu : u ≤ (o : ℝ)) :
    ((polyRelaxationFamily hd hσ).rel o).error l u < 1 / ((o : ℝ) + 1) :=
  (aux_exists_polyRelaxation_at_level hd hσ o).choose_spec.choose_spec l u hl hlu hu

/-- Some level covers every neuron's box and leaves `2 · error` under `ε`: the
range grows past the box and the tolerance falls under half the budget. -/
theorem aux_exists_level (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ o : ℕ, (∀ i, -(o : ℝ) ≤ s.interval.inf i ∧ s.interval.sup i ≤ (o : ℝ))
      ∧ 2 * (1 / ((o : ℝ) + 1)) ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  refine ⟨max M (Finset.univ.sup fun i : Fin n =>
    max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊), fun i => ?_, ?_⟩
  · -- the ceilings of both ends are under the supremum, hence under the level
    have hle := Finset.le_sup (f := fun i : Fin n =>
      max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊) (Finset.mem_univ i)
    have hcast : ∀ j : ℕ, j ≤ max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊ →
        (j : ℝ) ≤ (max M (Finset.univ.sup fun i : Fin n =>
          max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊) : ℕ) :=
      fun j hj => Nat.cast_le.mpr (le_trans (le_trans hj hle) (le_max_right _ _))
    have hlo := le_trans (Nat.le_ceil |s.interval.inf i|) (hcast _ (le_max_left _ _))
    have hhi := le_trans (Nat.le_ceil |s.interval.sup i|) (hcast _ (le_max_right _ _))
    exact ⟨by linarith [neg_abs_le (s.interval.inf i)],
      by linarith [le_abs_self (s.interval.sup i)]⟩
  · -- and the level is past `M`, which was chosen past `2 / ε`
    have hMo : (M : ℝ) ≤ ((max M (Finset.univ.sup fun i : Fin n =>
        max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (le_max_left _ _)
    have hopos : (0 : ℝ) < ((max M (Finset.univ.sup fun i : Fin n =>
        max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊) : ℕ) : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (max M (Finset.univ.sup fun i : Fin n =>
        max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊))]
    have h2 : 2 / ε < ((max M (Finset.univ.sup fun i : Fin n =>
        max ⌈|s.interval.inf i|⌉₊ ⌈|s.interval.sup i|⌉₊) : ℕ) : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at h2
    rw [mul_one_div, div_le_iff₀ hopos]
    linarith

/-- Refinement converges at the layer: raising the level puts the propagated set
inside any inflation of the exact image. -/
theorem Layer.activationPolyRefinable_convergent (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) :
    (Layer.activationPolyRefinable (n := n) (polyRelaxationFamily hd hσ)).Convergent := by
  intro s ε hε
  obtain ⟨o, hcov, hsmall⟩ := aux_exists_level s hε
  refine ⟨o, Layer.activationPoly_subset_inflate _ s hε.le fun i => ?_⟩
  -- the level's tolerance is under `ε / 2`, so twice the error is under `ε`
  have herr := polyRelaxationFamily_error_lt hd hσ o (hcov i).1
    (s.interval_inf_le_sup i) (hcov i).2
  linarith

end CORALean.Real
