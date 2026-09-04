import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `ConPolyZono.compact`

CORA's `@conPolyZono/compact_` at `'all'`: equal exponent columns are added
together and a column that came out zero is dropped, in the constraint matrix as
well as in the generators, and then the factors that fell out of use go. Exact.

Both merges are `PolyZonotope`'s. `sum_monomial_merge` is stated over exponent
data alone, so `A`'s columns — vectors in `Vec ℝ m` over the same `EC` — merge
by the very same lemma, `mulVec_eq_sum` reading `A μ(α)` as a generator sum.
Dropping factors is what does not carry over: `p` is shared, so only a factor
unused by *both* `E` and `EC` may go. `appendE` states the two as one matrix
over those shared factors, and `PolyZonotope.usedFactors` of it is the union.

CORA moves a column at exponent zero into the centre, and on the constraint side
into `b`; neither happens here, as neither does for `PolyZonotope.compact`.

Noncomputable for that operation's reason: dropping a zero column decides
whether an element of an arbitrary real module is zero.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-! ## The generators -/

/-- Equal exponent columns added together and the zero generators gone. The
whole constraint block stands, `p` included, so the constraint is untouched. -/
noncomputable def ConPolyZono.compactGens (C : ConPolyZono α) : ConPolyZono α where
  p := C.p
  h := (PolyZonotope.compactKeep C.E C.G).card
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep C.E) C.G
                  (PolyZonotope.compactIdx C.E C.G j)
  E := fun k j => C.E k (PolyZonotope.compactIdx C.E C.G j)
  GI := C.GI
  A := C.A
  b := C.b
  EC := C.EC

/-! ## The constraints -/

/-- Constraint column `l` as a vector, which is the generator the merge adds. -/
def ConPolyZono.consCol {m s : ℕ} (A : Mat ℝ m s) (l : Fin s) : Vec ℝ m := fun i => A i l

/-- `A μ(α)` read as a generator sum over the constraint columns, at the
monomials `EC` names — the form `sum_monomial_merge` merges. -/
theorem ConPolyZono.mulVec_eq_sum {m s : ℕ} (A : Mat ℝ m s) (v : Vec ℝ s) :
    A *ᵥ v = ∑ l, v l • ConPolyZono.consCol A l := by
  funext i
  show (∑ l, A i l * v l) = (∑ l, v l • ConPolyZono.consCol A l) i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound. -/
noncomputable def ConPolyZono.compactCons (C : ConPolyZono α) : ConPolyZono α where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := (PolyZonotope.compactKeep C.EC (ConPolyZono.consCol C.A)).card
  c := C.c
  G := C.G
  E := C.E
  GI := C.GI
  A := fun i l => PolyZonotope.fiberSum (PolyZonotope.rep C.EC) (ConPolyZono.consCol C.A)
                    (PolyZonotope.compactIdx C.EC (ConPolyZono.consCol C.A) l) i
  b := C.b
  EC := fun k l => C.EC k (PolyZonotope.compactIdx C.EC (ConPolyZono.consCol C.A) l)

/-! ## The factors -/

/-- The factors either block still reads. `appendE` puts both exponent matrices
over the shared factors, so this is `PolyZonotope.usedFactors` of one matrix and
denotes the union of the two used sets. -/
def ConPolyZono.usedFactors {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ) :
    Finset (Fin p) :=
  PolyZonotope.usedFactors (ConPolyZono.appendE E EC)

/-- The kept factors, indexed by a plain count, as `PolyZonotope`'s is. -/
def ConPolyZono.factorIdx {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (k : Fin (ConPolyZono.usedFactors E EC).card) : Fin p :=
  PolyZonotope.factorIdx (ConPolyZono.appendE E EC) k

/-- A factor vector over the kept factors, read back over all of them by giving a
dropped factor the value zero — admissible, and read by no monomial of either
block. -/
def ConPolyZono.factorExtend {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (k : Fin p) : ℝ :=
  PolyZonotope.factorExtend (ConPolyZono.appendE E EC) a k

theorem ConPolyZono.abs_factorExtend_le_one {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) {a : Fin (ConPolyZono.usedFactors E EC).card → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |ConPolyZono.factorExtend E EC a k| ≤ 1 :=
  PolyZonotope.abs_factorExtend_le_one (ConPolyZono.appendE E EC) ha k

/-- A generator monomial reads the kept factors and no others: it is a monomial
of `appendE`'s left half, and `monomial_factorIdx` holds of the whole. -/
theorem ConPolyZono.monomial_factorIdx_left {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) (i : Fin h) :
    PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E EC k) i)
        (fun k => a (ConPolyZono.factorIdx E EC k)) i
      = PolyZonotope.monomial E a i :=
  calc PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E EC k) i)
        (fun k => a (ConPolyZono.factorIdx E EC k)) i
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E EC k) i)
            fun k l => EC (ConPolyZono.factorIdx E EC k) l)
          (fun k => a (ConPolyZono.factorIdx E EC k)) (Fin.castAdd s i) :=
        (ConPolyZono.monomial_appendE_left _ _ _ i).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E EC) a (Fin.castAdd s i) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E EC) a (Fin.castAdd s i)
    _ = PolyZonotope.monomial E a i := ConPolyZono.monomial_appendE_left E EC a i

/-- The same at the constraint block, `appendE`'s right half. -/
theorem ConPolyZono.monomial_factorIdx_right {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) (l : Fin s) :
    PolyZonotope.monomial (fun k l => EC (ConPolyZono.factorIdx E EC k) l)
        (fun k => a (ConPolyZono.factorIdx E EC k)) l
      = PolyZonotope.monomial EC a l :=
  calc PolyZonotope.monomial (fun k l => EC (ConPolyZono.factorIdx E EC k) l)
        (fun k => a (ConPolyZono.factorIdx E EC k)) l
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E EC k) i)
            fun k l => EC (ConPolyZono.factorIdx E EC k) l)
          (fun k => a (ConPolyZono.factorIdx E EC k)) (Fin.natAdd h l) :=
        (ConPolyZono.monomial_appendE_right _ _ _ l).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E EC) a (Fin.natAdd h l) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E EC) a (Fin.natAdd h l)
    _ = PolyZonotope.monomial EC a l := ConPolyZono.monomial_appendE_right E EC a l

/-- The same generator monomial read against an extended factor vector, which is
what the reverse inclusion supplies. -/
theorem ConPolyZono.monomial_factorExtend_left {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (i : Fin h) :
    PolyZonotope.monomial E (ConPolyZono.factorExtend E EC a) i
      = PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E EC k) i) a i := by
  have hmon := ConPolyZono.monomial_factorIdx_left E EC (ConPolyZono.factorExtend E EC a) i
  have hext : (fun k => ConPolyZono.factorExtend E EC a (ConPolyZono.factorIdx E EC k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E EC) a k
  rw [hext] at hmon
  exact hmon.symm

/-- The same at the constraint block. -/
theorem ConPolyZono.monomial_factorExtend_right {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (l : Fin s) :
    PolyZonotope.monomial EC (ConPolyZono.factorExtend E EC a) l
      = PolyZonotope.monomial (fun k l => EC (ConPolyZono.factorIdx E EC k) l) a l := by
  have hmon := ConPolyZono.monomial_factorIdx_right E EC (ConPolyZono.factorExtend E EC a) l
  have hext : (fun k => ConPolyZono.factorExtend E EC a (ConPolyZono.factorIdx E EC k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E EC) a k
  rw [hext] at hmon
  exact hmon.symm

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand. -/
def ConPolyZono.compactFactors (C : ConPolyZono α) : ConPolyZono α where
  p := (ConPolyZono.usedFactors C.E C.EC).card
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.G
  E := fun k i => C.E (ConPolyZono.factorIdx C.E C.EC k) i
  GI := C.GI
  A := C.A
  b := C.b
  EC := fun k l => C.EC (ConPolyZono.factorIdx C.E C.EC k) l

/-- CORA's `compact`: the generators, then the constraints, then the factors.
The order matters in one direction only — dropping a column can leave a factor
unused, never the reverse. -/
noncomputable def ConPolyZono.compact (C : ConPolyZono α) : ConPolyZono α :=
  C.compactGens.compactCons.compactFactors

end CORALean.Real
