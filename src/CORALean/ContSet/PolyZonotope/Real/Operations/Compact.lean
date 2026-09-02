import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.compact`

CORA's `@polyZonotope/compact_`, which is `priv_removeRedundantExponents`
followed by dropping the factors that fall out of use. Three exact steps: equal
exponent columns are one monomial and are added together, a generator that came
out zero is dropped, and a factor at exponent zero in every remaining column is
dropped as well.

Without this the generator count is noise: `plus` and `quadMap` both grow it
while the set stands still, so an order bound counts columns that denote
nothing. `reduce` therefore compacts before it ranks.

Everything below the two `PolyZonotope`-level definitions is stated over
exponent data alone — an `E` and a family of generators over its columns, no set
and no representation. That is deliberate: a constrained polynomial zonotope's
constraint matrix `A` has columns over the very same exponent matrix `EC`, read
as generators in `Vec ℝ m`, so `sum_monomial_merge` applies to it unchanged.
Dropping factors is the one step that does *not* generalize by itself, since `p`
is shared between `E` and `EC` there and only a factor unused by *both* may go;
`usedFactors` would have to be handed the union. Nothing here prevents that, and
nothing here does it.

Merging needs to decide when two exponent columns agree, which is a
`DecidableEq (Fin p → ℕ)` and free. Dropping a zero generator needs to decide
whether an element of an arbitrary real module is zero, which is not: `compact`
is therefore noncomputable, and the merge picks its representative by `Fin h`'s
own order rather than by any ordering of the columns.

CORA also folds the all-zero column into the centre. That is exact too and is
left out: it is a fourth step with no bearing on either count, the constant
monomial being one generator whichever side of `c` it sits on.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The exponent column of generator `i`, which is the whole of what its
monomial is. -/
def PolyZonotope.col {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin p → ℕ :=
  fun k => E k i

theorem PolyZonotope.monomial_congr {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    {i j : Fin h} (hij : PolyZonotope.col E i = PolyZonotope.col E j) :
    PolyZonotope.monomial E a i = PolyZonotope.monomial E a j := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => congrArg (fun e => a k ^ e) (congrFun hij k)

/-- The generators a representative map gathers at `j`, added up: the one
generator their common column keeps. -/
def PolyZonotope.fiberSum {h : ℕ} (r : Fin h → Fin h) (G : Fin h → α) (j : Fin h) : α :=
  ∑ i ∈ Finset.univ.filter fun i => r i = j, G i

/-- Regrouping a generator sum along any column-preserving `r`, and then keeping
only the columns `s` names. Every step of `compact` on the generator side is
this lemma at a particular `r` and `s`, and it mentions no set: a constrained
representation reads its constraint columns as generators and reuses it. -/
theorem PolyZonotope.sum_monomial_merge {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (a : Fin p → ℝ) (r : Fin h → Fin h) (s : Finset (Fin h))
    (hcol : ∀ i, PolyZonotope.col E (r i) = PolyZonotope.col E i)
    (hs : ∀ j ∉ s, PolyZonotope.fiberSum r G j = 0) :
    (∑ i, PolyZonotope.monomial E a i • G i)
      = ∑ j ∈ s, PolyZonotope.monomial E a j • PolyZonotope.fiberSum r G j := by
  have hall : (∑ i, PolyZonotope.monomial E a i • G i)
      = ∑ j, PolyZonotope.monomial E a j • PolyZonotope.fiberSum r G j := by
    rw [← Finset.sum_fiberwise Finset.univ r fun i => PolyZonotope.monomial E a i • G i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PolyZonotope.fiberSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hri : r i = j := (Finset.mem_filter.mp hi).2
    have hcij : PolyZonotope.col E i = PolyZonotope.col E j := by
      rw [← hri]; exact (hcol i).symm
    rw [PolyZonotope.monomial_congr E a hcij]
  rw [hall]
  refine (Finset.sum_subset (Finset.subset_univ s) fun j _ hj => ?_).symm
  rw [hs j hj, smul_zero]

/-- The least index carrying the same exponent column. A canonical
representative per column is what makes the merge actually merge, and `Fin h`'s
own order supplies one: no order on the columns themselves is needed, only
equality on them. -/
def PolyZonotope.rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin h :=
  (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

theorem PolyZonotope.col_rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) :
    PolyZonotope.col E (PolyZonotope.rep E i) = PolyZonotope.col E i := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i)
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  exact (Finset.mem_filter.mp hmem).2

/-- The columns that survive: those whose merged generator is not zero. A column
that is not its class's representative has an empty fibre and so is dropped here
too, which is why merging and zero-dropping are one step. -/
noncomputable def PolyZonotope.compactKeep {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) : Finset (Fin h) :=
  @Finset.filter _ (fun j => PolyZonotope.fiberSum (PolyZonotope.rep E) G j ≠ 0)
    (Classical.decPred _) Finset.univ

omit [Module ℝ α] in
/-- Membership through the classical instance `compactKeep` fixes, which
instance search cannot rediscover at a use site. -/
theorem PolyZonotope.mem_compactKeep_iff {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) (j : Fin h) :
    j ∈ PolyZonotope.compactKeep E G ↔ PolyZonotope.fiberSum (PolyZonotope.rep E) G j ≠ 0 := by
  rw [PolyZonotope.compactKeep]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Module ℝ α] in
theorem PolyZonotope.fiberSum_eq_zero_of_notMem {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) {j : Fin h} (hj : j ∉ PolyZonotope.compactKeep E G) :
    PolyZonotope.fiberSum (PolyZonotope.rep E) G j = 0 :=
  not_not.mp fun hne => hj ((PolyZonotope.mem_compactKeep_iff E G j).mpr hne)

/-- The kept columns, indexed by a plain count — which is what the field `h`
needs and a `Finset` is not. -/
noncomputable def PolyZonotope.compactIdx {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (j : Fin (PolyZonotope.compactKeep E G).card) : Fin h :=
  (PolyZonotope.compactKeep E G).orderIsoOfFin rfl j

omit [Module ℝ α] in
theorem PolyZonotope.sum_compactKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (f : Fin h → α) :
    ∑ j ∈ PolyZonotope.compactKeep E G, f j
      = ∑ j, f (PolyZonotope.compactIdx E G j) := by
  rw [← Finset.sum_coe_sort (PolyZonotope.compactKeep E G) f]
  exact (Equiv.sum_comp ((PolyZonotope.compactKeep E G).orderIsoOfFin rfl).toEquiv
    fun x => f x).symm

/-- Equal exponent columns added together, and the zero generators gone. The
factors are untouched, so a factor vector carries over unchanged. -/
noncomputable def PolyZonotope.compactGens (PZ : PolyZonotope α) : PolyZonotope α where
  p := PZ.p
  h := (PolyZonotope.compactKeep PZ.E PZ.G).card
  q := PZ.q
  c := PZ.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep PZ.E) PZ.G
                  (PolyZonotope.compactIdx PZ.E PZ.G j)
  E := fun k j => PZ.E k (PolyZonotope.compactIdx PZ.E PZ.G j)
  GI := PZ.GI

/-- The factors some column still reads. -/
def PolyZonotope.usedFactors {p h : ℕ} (E : Fin p → Fin h → ℕ) : Finset (Fin p) :=
  Finset.univ.filter fun k => ∃ i, E k i ≠ 0

/-- The kept factors, indexed by a plain count, as `compactIdx` does for
columns. -/
def PolyZonotope.factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (k : Fin (PolyZonotope.usedFactors E).card) : Fin p :=
  (PolyZonotope.usedFactors E).orderIsoOfFin rfl k

/-- A factor vector over the kept factors, read back over all of them by giving
a dropped factor the value zero — admissible, and read by no monomial. -/
def PolyZonotope.factorExtend {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ) (k : Fin p) : ℝ :=
  if hk : k ∈ PolyZonotope.usedFactors E then
    a (((PolyZonotope.usedFactors E).orderIsoOfFin rfl).symm ⟨k, hk⟩)
  else 0

theorem PolyZonotope.abs_factorExtend_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin (PolyZonotope.usedFactors E).card → ℝ} (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |PolyZonotope.factorExtend E a k| ≤ 1 := by
  rw [PolyZonotope.factorExtend]
  split
  · exact ha _
  · rw [abs_zero]; exact zero_le_one

theorem PolyZonotope.factorExtend_factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ)
    (k : Fin (PolyZonotope.usedFactors E).card) :
    PolyZonotope.factorExtend E a (PolyZonotope.factorIdx E k) = a k := by
  have hmem : PolyZonotope.factorIdx E k ∈ PolyZonotope.usedFactors E :=
    ((PolyZonotope.usedFactors E).orderIsoOfFin rfl k).2
  rw [PolyZonotope.factorExtend, dif_pos hmem]
  congr 1
  rw [show (⟨PolyZonotope.factorIdx E k, hmem⟩ : {x // x ∈ PolyZonotope.usedFactors E})
      = (PolyZonotope.usedFactors E).orderIsoOfFin rfl k from Subtype.ext rfl]
  exact ((PolyZonotope.usedFactors E).orderIsoOfFin rfl).symm_apply_apply k

/-- A monomial reads the kept factors and no others, which is the whole content
of dropping a factor. -/
theorem PolyZonotope.monomial_factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    PolyZonotope.monomial (fun k i => E (PolyZonotope.factorIdx E k) i)
        (fun k => a (PolyZonotope.factorIdx E k)) i
      = PolyZonotope.monomial E a i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  have h1 : (∏ k, a (PolyZonotope.factorIdx E k) ^ E (PolyZonotope.factorIdx E k) i)
      = ∏ k ∈ PolyZonotope.usedFactors E, a k ^ E k i := by
    rw [← Finset.prod_coe_sort (PolyZonotope.usedFactors E) fun k => a k ^ E k i]
    exact Equiv.prod_comp ((PolyZonotope.usedFactors E).orderIsoOfFin rfl).toEquiv
      fun x => a x ^ E x i
  have h2 : (∏ k ∈ PolyZonotope.usedFactors E, a k ^ E k i) = ∏ k, a k ^ E k i := by
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have hz : E k i = 0 := by
      by_contra hne
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, ⟨i, hne⟩⟩)
    rw [hz, pow_zero]
  rw [h1, h2]

/-- The same monomial read against an extended factor vector: the extension
gives the dropped factors a value, and no monomial looks at it. -/
theorem PolyZonotope.monomial_factorExtend {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ) (i : Fin h) :
    PolyZonotope.monomial E (PolyZonotope.factorExtend E a) i
      = PolyZonotope.monomial (fun k i => E (PolyZonotope.factorIdx E k) i) a i := by
  have hmon := PolyZonotope.monomial_factorIdx E (PolyZonotope.factorExtend E a) i
  have hext : (fun k => PolyZonotope.factorExtend E a (PolyZonotope.factorIdx E k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx E a k
  rw [hext] at hmon
  exact hmon.symm

/-- The factors no column reads, dropped. Only `p` changes; every generator and
every column stands. -/
def PolyZonotope.compactFactors (PZ : PolyZonotope α) : PolyZonotope α where
  p := (PolyZonotope.usedFactors PZ.E).card
  h := PZ.h
  q := PZ.q
  c := PZ.c
  G := PZ.G
  E := fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i
  GI := PZ.GI

/-- CORA's `compact`: merge, drop, and drop again on the factor side. The order
matters in one direction only — dropping a generator can leave a factor unused,
never the reverse. -/
noncomputable def PolyZonotope.compact (PZ : PolyZonotope α) : PolyZonotope α :=
  PZ.compactGens.compactFactors

end CORALean.Real
