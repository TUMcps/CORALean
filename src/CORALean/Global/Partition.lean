module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Splitting an index type into parts

`Split α into β` names every index of `α` exactly once as `P.on k l`, where `k`
picks a part and `l` an index within it. Two parts are the common case and read
`Split α into βₗ ⊕ βᵣ`, with `P.left` and `P.right`.

`sum_split` is why the type exists: a sum over `α` splits along the parts with
no side condition, since the equivalence already rules out overlap.

The type is `Partition`; `Split` is only its notation, since naming the two
alike would make `Partition` a keyword. `ofPred` builds one out of a decidable
predicate, for a caller that only has one of those, such as a merge bucket.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

universe v


-- ========================================  MAIN TYPE  ========================================= --

structure Partition (α : Type*) {κ : Type*} (β : κ → Type*) where
  index : (Σ k, β k) ≃ α

/-- The two-part family. -/
def Pair (β γ : Type v) : Bool → Type v
  | true => β
  | false => γ

/-- Two parts, the common case. -/
abbrev Partition₂ (α : Type*) (β γ : Type v) := Partition α (Pair β γ)

scoped notation:50 "Split " α:max " into " β:max => CORALean.Partition α β
scoped notation:50 "Split " α:max " into " β:max " ⊕ " γ:max => CORALean.Partition₂ α β γ

instance {β γ : Type v} [Fintype β] [Fintype γ] : (b : Bool) → Fintype (Pair β γ b)
  | true => inferInstanceAs (Fintype β)
  | false => inferInstanceAs (Fintype γ)

variable {α α' κ M : Type*} {β : κ → Type*} {βₗ βᵣ : Type v}

def Pair.equivSum (β γ : Type v) : (Σ b, Pair β γ b) ≃ β ⊕ γ where
  toFun := fun ⟨b, x⟩ => match b, x with
    | true, x => Sum.inl x
    | false, x => Sum.inr x
  invFun := fun s => match s with
    | Sum.inl x => ⟨true, x⟩
    | Sum.inr x => ⟨false, x⟩
  left_inv := by rintro ⟨(_ | _), x⟩ <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- Split at `q`, first part first: `left` is `Fin.castAdd` and `right` is
`Fin.natAdd`, both by `rfl`. -/
def Partition.split (q r : ℕ) : Split (Fin (q + r)) into (Fin q) ⊕ (Fin r) where
  index := (Pair.equivSum (Fin q) (Fin r)).trans finSumFinEquiv

/-- Rename what a partition splits: every selection rule is `split` composed with
the permutation that orders the indices. -/
def Partition.reindex (P : Split α into βₗ ⊕ βᵣ) (e : α' ≃ α) : Split α' into βₗ ⊕ βᵣ where
  index := P.index.trans e.symm

/-- The indices satisfying `p`, counted off in increasing order. `Fintype.equivFin`
would do as well and does not compute; sorting the `Finset` does. -/
def Partition.finSubtypeEquiv {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Fin (Fintype.card {i : Fin n // p i}) ≃ {i : Fin n // p i} :=
  ((Finset.univ.filter p).orderIsoOfFin (by rw [Fintype.card_subtype])).toEquiv.trans
    (Equiv.subtypeEquivRight fun i => by simp)

/-- The split a decidable predicate cuts `Fin n` into: the neurons failing `p`
survive on the left, those satisfying it are the bucket on the right, each in
increasing order. It computes wherever `p` is decided by a computation. -/
def Partition.ofPred {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Split (Fin n) into (Fin (Fintype.card {i : Fin n // ¬ p i}))
      ⊕ (Fin (Fintype.card {i : Fin n // p i})) where
  index := ((Pair.equivSum _ _).trans
      (Equiv.sumCongr (Partition.finSubtypeEquiv fun i => ¬ p i)
        (Partition.finSubtypeEquiv p))).trans
    ((Equiv.sumComm {i : Fin n // ¬ p i} {i : Fin n // p i}).trans (Equiv.sumCompl p))

def Partition.on (P : Split α into β) (k : κ) (l : β k) : α := P.index ⟨k, l⟩

def Partition.left (P : Split α into βₗ ⊕ βᵣ) (l : βₗ) : α := P.on true l

def Partition.right (P : Split α into βₗ ⊕ βᵣ) (l : βᵣ) : α := P.on false l

/-- Every bucket index satisfies the predicate it was cut out by. -/
theorem Partition.ofPred_right {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (l : Fin (Fintype.card {i : Fin n // p i})) :
    p ((Partition.ofPred p).right l) :=
  (Partition.finSubtypeEquiv p l).property

/-- Every surviving index fails the predicate that cut out the bucket. -/
theorem Partition.ofPred_left {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (l : Fin (Fintype.card {i : Fin n // ¬ p i})) :
    ¬ p ((Partition.ofPred p).left l) :=
  (Partition.finSubtypeEquiv (fun i => ¬ p i) l).property

theorem Partition.sum_split [AddCommMonoid M] [Fintype α] [Fintype κ] [∀ k, Fintype (β k)]
    (P : Split α into β) (f : α → M) :
    ∑ j, f j = ∑ k, ∑ l, f (P.on k l) := by
  rw [← Equiv.sum_comp P.index f, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

theorem Partition.sum_split₂ [AddCommMonoid M] [Fintype α] [Fintype βₗ] [Fintype βᵣ]
    (P : Split α into βₗ ⊕ βᵣ) (f : α → M) :
    ∑ j, f j = ∑ l, f (P.left l) + ∑ l, f (P.right l) := by
  rw [P.sum_split f, Fintype.sum_bool]
  rfl

/-- A matrix-vector product splits along a partition of the columns, as `sum_split₂` splits a
sum: what neuron merging parts into the survivors' weights and the bucket's contribution. -/
theorem Partition.mulVec_split₂ {ι R : Type*} [Fintype α] [Fintype βₗ] [Fintype βᵣ]
    [NonUnitalNonAssocSemiring R] (P : Split α into βₗ ⊕ βᵣ) (W : Matrix ι α R)
    (v : α → R) : -- --- STMT ---
    W.mulVec v
      = (W.submatrix id P.left).mulVec (v ∘ P.left)
        + (W.submatrix id P.right).mulVec (v ∘ P.right) := by -- --- PROOF ---
  funext i
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
    Function.comp]
  exact P.sum_split₂ fun j => W i j * v j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
