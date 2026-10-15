module

public import CORALean.Specification.FourValued.Operations.And
public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValued.Operations.Not
public import CORALean.Specification.FourValued.Operations.Or
public import CORALean.Specification.Kleene.Operations.And
public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.Kleene.Operations.Or
public import CORALean.Specification.FourValued.Instances
public import CORALean.Specification.Kleene.Instances
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# `FourValued/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

`le_iff` and `fromKleene_le_iff` are the truth order of [1, Sec. 2.2 (order)], with
`truthOrder_spec` in its own file;
`and_eq_join`, `or_eq_join`, `not_eq_join` and `uu_and_ii` are [1, Fig. 3], and `join_floor_ceil`
and `isRefinedBy_iff` the characterization of `≺` in [1, Sec. 4.3 (refinements)].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ==================================  `FourValued.and_assoc`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is associative. -/
theorem FourValued.and_assoc (a b c : FourValued) : (a.and b).and c = a.and (b.and c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ==================================  `FourValued.and_comm`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is commutative. -/
theorem FourValued.and_comm (a b : FourValued) : a.and b = b.and a := by
  cases a <;> cases b <;> rfl


-- =================================  `FourValued.and_eq_join`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fig. 3`: `a & b` is the `⊔₂` of the Kleene conjunction of the underapproximations
`⌊a⌋ ∧ ⌊b⌋` and that of the overapproximations `⌈a⌉ ∧ ⌈b⌉`. -/
theorem FourValued.and_eq_join (a b : FourValued) :
    a.and b = FourValued.join (a.floor.and b.floor) (a.ceil.and b.ceil) := by
  cases a <;> cases b <;> rfl


-- ===================================  `FourValued.and_ff`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `False` absorbs under `&`. -/
theorem FourValued.and_ff (a : FourValued) : a.and .ff = .ff := by
  cases a <;> rfl


-- ===================================  `FourValued.and_ii`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An inconclusive operand makes `&` inconclusive unless the result is already false. -/
theorem FourValued.and_ii (a : FourValued) :
    a.and .ii = if a = .ff then .ff else .ii := by
  cases a <;> rfl


-- ==============================  `FourValued.and_or_distrib_ne`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` does not distribute over `|`: `Unknown & (Inconclusive | True) = Unknown`. -/
theorem FourValued.and_or_distrib_ne :
    FourValued.uu.and (FourValued.ii.or .tt) ≠
      (FourValued.uu.and .ii).or (FourValued.uu.and .tt) := nofun


-- ===============================  `FourValued.and_or_self_ne`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption fails: `Unknown & (Unknown | Inconclusive)` is not `Unknown`. -/
theorem FourValued.and_or_self_ne :
    FourValued.uu.and (FourValued.uu.or .ii) ≠ .uu := nofun


-- ==================================  `FourValued.and_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is idempotent. -/
theorem FourValued.and_self (a : FourValued) : a.and a = a := by
  cases a <;> rfl


-- ===================================  `FourValued.and_tt`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `True` is the unit of `&`. -/
theorem FourValued.and_tt (a : FourValued) : a.and .tt = a := by
  cases a <;> rfl


-- ===========================  `FourValued.fromBool_eq_fromKleene`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` factors through the Kleene one. -/
theorem FourValued.fromBool_eq_fromKleene (b : Bool) :
    FourValued.fromBool b = FourValued.fromKleene (Kleene.fromBool b) := by
  cases b <;> rfl


-- ===============================  `FourValued.fromKleene_and`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `&`. -/
theorem FourValued.fromKleene_and (a b : Kleene) :
    FourValued.fromKleene (a.and b) = (FourValued.fromKleene a).and (FourValued.fromKleene b) := by
  cases a <;> cases b <;> rfl


-- ============================  `FourValued.fromKleene_eq_ff_iff`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` gives `False` only for `False`. -/
theorem FourValued.fromKleene_eq_ff_iff (k : Kleene) :
    FourValued.fromKleene k = FourValued.ff ↔ k = Kleene.ff := by
  cases k <;> simp [FourValued.fromKleene]


-- ============================  `FourValued.fromKleene_eq_tt_iff`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` gives `True` only for `True`. -/
theorem FourValued.fromKleene_eq_tt_iff (k : Kleene) :
    FourValued.fromKleene k = FourValued.tt ↔ k = Kleene.tt := by
  cases k <;> simp [FourValued.fromKleene]


-- ===============================  `FourValued.fromKleene_not`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `~`. -/
theorem FourValued.fromKleene_not (a : Kleene) :
    FourValued.fromKleene a.not = (FourValued.fromKleene a).not := by
  cases a <;> rfl


-- ================================  `FourValued.fromKleene_or`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `|`. -/
theorem FourValued.fromKleene_or (a b : Kleene) :
    FourValued.fromKleene (a.or b) = (FourValued.fromKleene a).or (FourValued.fromKleene b) := by
  cases a <;> cases b <;> rfl


-- ===============================  `FourValued.isRefinedBy_iff`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `v` is refined by `k` iff `⌊v⌋ ⊑ₜ k ⊑ₜ ⌈v⌉`, [1, Sec. 4.3 (refinements)]. -/
theorem FourValued.isRefinedBy_iff (v : FourValued) (k : Kleene) :
    v.IsRefinedBy k ↔ v.floor ≤ k ∧ k ≤ v.ceil := by
  cases v <;> cases k <;> simp [FourValued.IsRefinedBy, FourValued.floor, FourValued.ceil,
    FourValued.fromKleene, Kleene.le_iff_code, Kleene.code]


-- ===============================  `FourValued.join_floor_ceil`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `v = ⌊v⌋ ⊔₂ ⌈v⌉`, [1, Sec. 4.3 (refinements)]. -/
theorem FourValued.join_floor_ceil (v : FourValued) : FourValued.join v.floor v.ceil = v := by
  cases v <;> rfl


-- ===================================  `FourValued.le_iff`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `v ⊑ₜ v'` iff `v = v'`, or `v` is `False`, or `v'` is `True`. -/
theorem FourValued.le_iff (a b : FourValued) :
    a ≤ b ↔ a = b ∨ a = FourValued.ff ∨ b = FourValued.tt := Iff.rfl


-- ==============================  `FourValued.fromKleene_le_iff`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The order on `U₂` restricts to that on `U₁`, [1, Sec. 2.2 (order)]. -/
theorem FourValued.fromKleene_le_iff (a b : Kleene) :
    FourValued.fromKleene a ≤ FourValued.fromKleene b ↔ a ≤ b := by
  cases a <;> cases b <;> simp [FourValued.le_iff, Kleene.le_iff_code, Kleene.code,
    FourValued.fromKleene]


-- ===================================  `FourValued.not_and`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a & b) = ~a | ~b`. -/
theorem FourValued.not_and (a b : FourValued) : (a.and b).not = a.not.or b.not := by
  cases a <;> cases b <;> rfl


-- =================================  `FourValued.not_eq_join`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fig. 3`: `~a` is the `⊔₂` of `~⌊a⌋` and `~⌈a⌉`. -/
theorem FourValued.not_eq_join (a : FourValued) :
    a.not = FourValued.join a.floor.not a.ceil.not := by
  cases a <;> rfl


-- ===================================  `FourValued.not_not`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~~a = a`. -/
theorem FourValued.not_not (a : FourValued) : a.not.not = a := by
  cases a <;> rfl


-- ===============================  `FourValued.not_ofKleeneInc`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negation negates the Kleene part and keeps the inconclusive flag. -/
theorem FourValued.not_ofKleeneInc (k : Kleene) (inc : Bool) :
    (FourValued.ofKleeneInc k inc).not = FourValued.ofKleeneInc k.not inc := by
  cases k <;> cases inc <;> rfl


-- ===================================  `FourValued.not_or`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a | b) = ~a & ~b`. -/
theorem FourValued.not_or (a b : FourValued) : (a.or b).not = a.not.and b.not := by
  cases a <;> cases b <;> rfl


-- =====================  `FourValued.ofKleeneInc_toKleene_isInconclusive`  ===================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Splitting a value into its Kleene part and flag and joining them is the identity. -/
theorem FourValued.ofKleeneInc_toKleene_isInconclusive (a : FourValued) :
    FourValued.ofKleeneInc a.toKleene a.isInconclusive = a := by
  cases a <;> rfl


-- ==============================  `FourValued.or_and_distrib_ne`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` does not distribute over `&`: `Unknown | (False & Inconclusive) = Unknown`. -/
theorem FourValued.or_and_distrib_ne :
    FourValued.uu.or (FourValued.ff.and .ii) ≠
      (FourValued.uu.or .ff).and (FourValued.uu.or .ii) := nofun


-- ===============================  `FourValued.or_and_self_ne`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption fails: `Unknown | (Unknown & Inconclusive)` is not `Unknown`. -/
theorem FourValued.or_and_self_ne :
    FourValued.uu.or (FourValued.uu.and .ii) ≠ .uu := nofun


-- ==================================  `FourValued.or_assoc`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is associative. -/
theorem FourValued.or_assoc (a b c : FourValued) : (a.or b).or c = a.or (b.or c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ===================================  `FourValued.or_comm`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is commutative. -/
theorem FourValued.or_comm (a b : FourValued) : a.or b = b.or a := by
  cases a <;> cases b <;> rfl


-- =================================  `FourValued.or_eq_join`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fig. 3`: `a | b` is the `⊔₂` of the Kleene disjunctions of the under- and the
overapproximations. -/
theorem FourValued.or_eq_join (a b : FourValued) :
    a.or b = FourValued.join (a.floor.or b.floor) (a.ceil.or b.ceil) := by
  cases a <;> cases b <;> rfl


-- ====================================  `FourValued.or_ff`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `False` is the unit of `|`. -/
theorem FourValued.or_ff (a : FourValued) : a.or .ff = a := by
  cases a <;> rfl


-- ====================================  `FourValued.or_ii`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An inconclusive operand makes `|` inconclusive unless the result is already true. -/
theorem FourValued.or_ii (a : FourValued) :
    a.or .ii = if a = .tt then .tt else .ii := by
  cases a <;> rfl


-- ===================================  `FourValued.or_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is idempotent. -/
theorem FourValued.or_self (a : FourValued) : a.or a = a := by
  cases a <;> rfl


-- ====================================  `FourValued.or_tt`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `True` absorbs under `|`. -/
theorem FourValued.or_tt (a : FourValued) : a.or .tt = .tt := by
  cases a <;> rfl


-- ==================================  `FourValued.uu_and_ii`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fig. 3`: `⊣₁ ∧ ⊣₂ = ⊣₂`, the join of `⊣₁ ∧ ⊥ = ⊥` and `⊣₁ ∧ ⊤ = ⊣₁`. -/
theorem FourValued.uu_and_ii :
    FourValued.uu.and .ii = .ii ∧
      FourValued.uu.and .ii = FourValued.join (Kleene.uu.and .ff) (Kleene.uu.and .tt) := ⟨rfl, rfl⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
