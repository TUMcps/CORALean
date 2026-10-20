module

public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffGenRec
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `Zonotope.minkDiffGenRec` computes the Minkowski difference exactly

[1, Thm. 1]: the generator recursion is not an enclosure, it is the difference. The paper's own
argument — write `Zₛ = c⁽ˢ⁾ ⊕ ⊕ᵢ [-1,1]⊗g⁽ˢ'ⁱ⁾`, recurse through `minkowskiDiff_add_assoc` (its
eq. (6)), then read each single-generator difference off the two extreme coefficients (eq. (8)) —
is carried through by induction on the generator count, peeling one index at a time with
`Fin.foldl_succ` and `Fin.sum_univ_succ`. Convexity of the running set makes the two-extremes step
exact, and the paper leaves it unsaid: eq. (8) is stated "for a set `A`", and at the non-convex
`A = {-1, 1} ⊆ ℝ` with `g = 1` the left side is `∅` and the right `{0}`. Here the running set
stays convex (intersections of translates of a zonotope), carried along the induction.

## Inputs
* `Zm` – minuend
* `Zs` – subtrahend

## Hypotheses
* none

## Conclusion
* the generator recursion gives the Minkowski difference exactly

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- Both translates at once: `x` lies in `A + {v}` and in `A - {v}` exactly when
shifting it either way along `v` lands in `A`. -/
theorem aux_mem_translates (A : Set α) (v x : α) : -- --- CONCL ---
    x ∈ (A + ({v} : Set α)) ∩ (A - ({v} : Set α)) ↔ x - v ∈ A ∧ x + v ∈ A := by -- --- PROOF ---
  constructor
  · rintro ⟨⟨a, ha, b, hb, hx⟩, a', ha', b', hb', hx'⟩
    -- the singleton pins each second witness, so each shift is the witness itself
    rw [Set.mem_singleton_iff] at hb hb'
    refine ⟨?_, ?_⟩
    · rw [← hx, hb]; simpa using ha
    · rw [← hx', hb']; simpa using ha'
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x - v, h1, v, rfl, by simp⟩, x + v, h2, v, rfl, by simp⟩

/-- The zero-centered zonotope on `n + 1` generators splits its head off: the
segment generator `0` spans, plus the zonotope on the remaining generators. -/
theorem aux_construct_succ (n : ℕ) (g : Fin (n + 1) → α) : -- --- CONCL ---
    (⟨n + 1, (0 : α), g⟩ : Zonotope α).construct
      = {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g 0}
          + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨β, hβ, rfl⟩
    -- the head coefficient is the segment's, the tail is the smaller zonotope's
    refine ⟨β 0 • g 0, ⟨β 0, hβ 0, rfl⟩, ∑ k : Fin n, β k.succ • g k.succ,
      ⟨fun k => β k.succ, fun k => hβ k.succ, (zero_add _).symm⟩, ?_⟩
    simp only [Fin.sum_univ_succ]
    abel
  · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    -- and back: `Fin.cons` is what puts the two coefficient families together
    refine ⟨Fin.cons t β, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using ht
      · intro k; simpa using hβ k
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      abel

/-- What [1, Thm. 1]'s proof calls eq. (8): a *convex* set's difference by the
segment one generator spans is its intersection with both translates. -/
theorem aux_minkowskiDiff_seg (A : Set α) (hA : Convex ℝ A) (v : α) : -- --- CONCL ---
    minkowskiDiff A {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • v}
      = (A + ({v} : Set α)) ∩ (A - ({v} : Set α)) := by -- --- PROOF ---
  ext x
  rw [aux_mem_translates]
  constructor
  · intro hx
    -- only the two extreme coefficients are read off, which is the paper's step
    refine ⟨?_, ?_⟩
    · have h := hx ((-1 : ℝ) • v) ⟨-1, by norm_num, rfl⟩
      rwa [neg_one_smul, ← sub_eq_add_neg] at h
    · have h := hx ((1 : ℝ) • v) ⟨1, by norm_num, rfl⟩
      rwa [one_smul] at h
  · rintro ⟨e1, e2⟩ y ⟨t, ht, rfl⟩
    -- every interior coefficient is a convex combination of those two
    have hc1 : (0 : ℝ) ≤ (1 - t) / 2 := by linarith [(abs_le.mp ht).2]
    have hc2 : (0 : ℝ) ≤ (1 + t) / 2 := by linarith [(abs_le.mp ht).1]
    have hmem := hA e1 e2 hc1 hc2 (by ring)
    have heq : ((1 - t) / 2) • (x - v) + ((1 + t) / 2) • (x + v) = x + t • v := by module
    rwa [heq] at hmem

/-- The fold over `n` generators is the Minkowski difference by the zonotope they
span, at every convex starting set — the induction the recursion needs. -/
theorem aux_fold_eq_minkDiff (n : ℕ) : -- --- CONCL ---
    ∀ (g : Fin n → α) (A : Set α), Convex ℝ A →
      Fin.foldl n (fun A i => (A + {g i}) ∩ (A - {g i})) A
        = minkowskiDiff A (⟨n, (0 : α), g⟩ : Zonotope α).construct := by -- --- PROOF ---
  induction n with
  | zero =>
    intro g A _
    -- no generators: the zonotope is `{0}` and subtracting it changes nothing
    have hc : (⟨0, (0 : α), g⟩ : Zonotope α).construct = ({(0 : α)} : Set α) := by
      ext y
      constructor
      · rintro ⟨β, -, hy⟩
        simpa using hy
      · rintro rfl
        exact ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    rw [Fin.foldl_zero, hc]
    ext x
    constructor
    · intro hx y hy
      rw [Set.mem_singleton_iff.mp hy, add_zero]
      exact hx
    · intro hx
      have h := hx (0 : α) rfl
      rwa [add_zero] at h
  | succ n ih =>
    intro g A hA
    -- one fold step is one generator peeled off, and it keeps the set convex
    have hAconv : Convex ℝ ((A + {g 0}) ∩ (A - {g 0})) :=
      (hA.add (convex_singleton (g 0))).inter (hA.sub (convex_singleton (g 0)))
    simp only [Fin.foldl_succ]
    rw [ih (fun i => g i.succ) ((A + {g 0}) ∩ (A - {g 0})) hAconv, aux_construct_succ n g,
      minkowskiDiff_add_assoc, aux_minkowskiDiff_seg A hA (g 0)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the generator recursion computes the Minkowski difference
exactly, not merely an enclosure of it. -/
theorem Zonotope.minkDiffGenRec_exact (Zm Zs : Zonotope α) : -- --- CONCL ---
    Zm.minkDiffGenRec Zs = minkowskiDiff Zm.construct Zs.construct := by -- --- PROOF ---
  have hA : Convex ℝ (Zm.construct - {Zs.c}) := Zm.convex_construct.sub (convex_singleton Zs.c)
  -- the subtrahend is its center plus the zonotope its generators span
  have hcenter : Zs.construct = {Zs.c} + (⟨Zs.h, (0 : α), Zs.G⟩ : Zonotope α).construct := by
    ext y
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨Zs.c, rfl, ∑ j, β j • Zs.G j, ⟨β, hβ, (zero_add _).symm⟩, rfl⟩
    · rintro ⟨_, rfl, _, ⟨β, hβ, rfl⟩, rfl⟩
      exact ⟨β, hβ, by rw [zero_add]⟩
  -- and subtracting a center is the `Z_int⁽¹⁾` the recursion starts from
  have hsingle : minkowskiDiff Zm.construct ({Zs.c} : Set α) = Zm.construct - {Zs.c} := by
    ext x
    constructor
    · intro hx
      exact ⟨x + Zs.c, hx Zs.c rfl, Zs.c, rfl, by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩ y hy
      rw [Set.mem_singleton_iff.mp hy, Set.mem_singleton_iff.mp hb]
      simpa using ha
  rw [Zonotope.minkDiffGenRec, aux_fold_eq_minkDiff Zs.h Zs.G _ hA, ← hsingle,
    ← minkowskiDiff_add_assoc, ← hcenter]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
