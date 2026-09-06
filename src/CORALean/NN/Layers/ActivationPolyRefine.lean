import CORALean.NN.Layers.ActivationPolyInflate
import CORALean.NN.Layers.PolyRangeConvergence
import CORALean.NN.Layers.PolyRelaxationPad
import CORALean.NN.Operations.Convergent

/-!
# The activation layer as a refinable layer

The refinement loop's one interesting layer [1]. A `PolyRelaxationFamily` is a
relaxation per level, the order free to grow with it, and the layer reads an
order pattern as one index into that family per neuron — every level is sound,
so the schedule decides precision alone.

The neurons' orders differ, so their fits do; `atPattern` pads each to the
layer's largest degree, which is exact, so one coefficient list still serves.

`polyRelaxationFamily` is the family a loop actually runs: level `o` fits `σ` on
`[-o, o]` to within `1 / (o + 1)`. A polynomial is unbounded, so no single fit
serves every input set, and a level has to say where it is accurate as well as
how accurately.

It is built by choice, `exists_polyRelaxation_error_lt` being an existence
statement: CORA's `poly_method` is one witness of many, and `sound` answers for
every one of them.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet

variable {σ σ' : ℝ → ℝ} {Mσ : ℝ} {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A polynomial relaxation per refinement level, the order free to grow. -/
structure PolyRelaxationFamily (σ : ℝ → ℝ) where
  deg : ℕ → ℕ
  rel : (o : ℕ) → PolyRelaxation σ (deg o)

/-- The degree a whole layer is read at: the largest any of its neurons asks
for, which padding lifts the others to. -/
def PolyRelaxationFamily.degOf (F : PolyRelaxationFamily σ) (t : OrderPattern n) : ℕ :=
  Finset.univ.sup fun i => F.deg (t i)

/-- Every neuron's own degree is under the layer's, which is what padding needs
and what makes the common degree no restriction. -/
theorem PolyRelaxationFamily.deg_le_degOf (F : PolyRelaxationFamily σ) (t : OrderPattern n)
    (i : Fin n) : F.deg (t i) ≤ F.degOf t :=
  Finset.le_sup (f := fun j => F.deg (t j)) (Finset.mem_univ i)

/-- The layer's abstraction at an order pattern: each neuron's own fit at its
own level, padded to the common degree. -/
def PolyRelaxationFamily.atPattern (F : PolyRelaxationFamily σ) (t : OrderPattern n) :
    LayerRelaxation σ n (F.degOf t) :=
  fun i => (F.rel (t i)).padTo (F.degOf t) (F.deg_le_degOf t i)

/-- The activation layer of a family: one `σ`, one enclosure per pattern. -/
noncomputable def Layer.activationPolyRefinable (F : PolyRelaxationFamily σ) :
    RefinableLayer 𝒫𝒵 n n where
  eval x := fun i => σ (x i)
  propagate t := (Layer.activationPoly (F.atPattern t)).propagate
  propagate_outer t := (Layer.activationPoly (F.atPattern t)).propagate_outer


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

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

/-- The level one neuron needs: past both ends of its own box, and past `2 / ε`
so that twice the tolerance fits under the budget. -/
theorem aux_exists_level_one (l u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ o : ℕ, (-(o : ℝ) ≤ l ∧ u ≤ (o : ℝ)) ∧ 2 * (1 / ((o : ℝ) + 1)) ≤ ε := by -- --- PROOF ---
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  -- one level past `M` and past both ceilings serves this neuron
  obtain ⟨o, hMo, hlo, huo⟩ : ∃ o : ℕ, M ≤ o ∧ ⌈|l|⌉₊ ≤ o ∧ ⌈|u|⌉₊ ≤ o :=
    ⟨max M (max ⌈|l|⌉₊ ⌈|u|⌉₊), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hl : |l| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hlo)
  have hu : |u| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr huo)
  have hMr : (M : ℝ) ≤ (o : ℝ) := Nat.cast_le.mpr hMo
  have hopos : (0 : ℝ) < (o : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) o]
  refine ⟨o, ⟨by linarith [neg_abs_le l], by linarith [le_abs_self u]⟩, ?_⟩
  -- the level is past `M`, which was chosen past `2 / ε`
  have h2 : 2 / ε < (o : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at h2
  rw [mul_one_div, div_le_iff₀ hopos]
  linarith

/-- A level per neuron, each covering that neuron's own box and leaving
`2 · error` under `ε`: nothing waits for the widest box in the layer. -/
theorem aux_exists_level (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : OrderPattern n, ∀ i,
      (-((t i : ℕ) : ℝ) ≤ s.interval.inf i ∧ s.interval.sup i ≤ ((t i : ℕ) : ℝ))
        ∧ 2 * (1 / (((t i : ℕ) : ℝ) + 1)) ≤ ε :=
  ⟨fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose,
    fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose_spec⟩

/-- Refinement converges at the layer: raising the pattern puts the propagated
set inside any inflation of the exact image. -/
theorem Layer.activationPolyRefinable_convergent (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hσ : ∀ x, |σ' x| ≤ Mσ) :
    (Layer.activationPolyRefinable
      (n := n) (polyRelaxationFamily hd hσ)).Convergent := by -- --- PROOF ---
  intro s ε hε
  obtain ⟨t, ht⟩ := aux_exists_level s hε
  refine ⟨t, Layer.activationPoly_subset_inflate
    ((polyRelaxationFamily hd hσ).atPattern t) s hε.le fun i => ?_⟩
  -- padding leaves the error alone, so the neuron's own level is what counts
  have hpad : ((polyRelaxationFamily hd hσ).atPattern t i).error
      = ((polyRelaxationFamily hd hσ).rel (t i)).error := rfl
  rw [hpad]
  have herr := polyRelaxationFamily_error_lt hd hσ (t i) (ht i).1.1
    (s.interval_inf_le_sup i) (ht i).1.2
  linarith [(ht i).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
