module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.IsBox
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `ZonoBundle.isIntervalCora`

What `@zonoBundle/representsa_` computes for the type `'interval'`: `n == 1 || aux_isInterval(zB,
tol)`, where `aux_isInterval` is `true` in dimension one and for an empty set, and otherwise loops
`for i = 1:zB.parallelSets` over `representsa_(zB.Z{1}, 'interval', tol)`. The loop variable `i` is
never used: it tests the first member `Z{1}` `parallelSets` times, so a bundle whose *first* member
is a box passes whatever the others are. Read from the source, not run.

# CORA's `zonoBundle/representsa_` calls a segment an interval

The bundle of the box `[-1, 1]²` and the diagonal segment `{(t, t) : |t| ≤ 1}` denotes that segment,
which is not an axis-aligned box. `aux_isInterval` tests `zB.Z{1}`, the box, in every pass of its
loop, never `zB.Z{2}`, so `representsa_(zB, 'interval')` answers `true`. Read from the source,
not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's test: `n = 1`, or an empty set, or every pass of the loop finds `Z{1}` a box. -/
def ZonoBundle.isIntervalCora (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) : Prop :=
  n = 1 ∨ zB.construct = ∅ ∨ ∀ _i : Fin zB.k, (zB.Z ⟨0, hk⟩).IsBox


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isIntervalCora_counterexample :
    ∃ (zB : ZonoBundle (Vec ℝ 2)) (hk : 0 < zB.k), zB.isIntervalCora hk
      ∧ ¬ ∃ I : Interval (Vec ℝ 2), zB.construct = I.construct := by -- --- PROOF ---
  -- the box and the diagonal
  let Z₁ : Zonotope (Vec ℝ 2) := ⟨2, fun _ => 0, fun j => Pi.single j 1⟩
  let Z₂ : Zonotope (Vec ℝ 2) := ⟨1, fun _ => 0, fun _ _ => 1⟩
  let zB : ZonoBundle (Vec ℝ 2) := ⟨2, fun i => if i = 0 then Z₁ else Z₂⟩
  have hk : 0 < zB.k := Nat.two_pos
  have h10 : ¬ ((1 : Fin 2) = 0) := by simp
  -- the box is the unit cube, the diagonal the points with equal coordinates in `[-1, 1]`
  have hZ₁ : ∀ x : Vec ℝ 2, x ∈ Z₁.construct ↔ ∀ i, |x i| ≤ 1 := by
    intro x
    constructor
    · rintro ⟨β, hβ, rfl⟩ i
      simpa [Z₁, Finset.sum_apply, Pi.single_apply] using hβ i
    · intro hx
      refine ⟨x, hx, ?_⟩
      funext i
      simp [Z₁, Finset.sum_apply, Pi.single_apply]
  -- the diagonal
  have hZ₂ : ∀ x : Vec ℝ 2, x ∈ Z₂.construct ↔ ∃ t : ℝ, |t| ≤ 1 ∧ ∀ i, x i = t := by
    intro x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β 0, hβ 0, fun i => by simp [Z₂]⟩
    · rintro ⟨t, ht, hx⟩
      refine ⟨fun _ => t, fun _ => ht, ?_⟩
      funext i
      simp [Z₂, hx i]
  -- the bundle is the diagonal inside the cube
  have hmem : ∀ x : Vec ℝ 2, x ∈ zB.construct ↔
      (∀ i, |x i| ≤ 1) ∧ ∃ t : ℝ, |t| ≤ 1 ∧ ∀ i, x i = t := by
    intro x
    simp only [ZonoBundle.construct, Set.mem_iInter]
    rw [Fin.forall_fin_two]
    simp only [zB, if_pos, h10, if_false, hZ₁, hZ₂]
  have hIc : ∀ (J : Interval (Vec ℝ 2)) (x : Vec ℝ 2),
      x ∈ J.construct ↔ ∀ i, J.inf i ≤ x i ∧ x i ≤ J.sup i := fun _ _ => Iff.rfl
  refine ⟨zB, hk, Or.inr (Or.inr fun _ => ⟨⟨fun _ => -1, fun _ => 1⟩, ?_⟩), ?_⟩
  · -- the first member is the box `[-1, 1]²`
    ext x
    have h00 : (⟨0, hk⟩ : Fin zB.k) = 0 := rfl
    show x ∈ (if (⟨0, hk⟩ : Fin zB.k) = 0 then Z₁ else Z₂).construct ↔ _
    rw [if_pos h00, hZ₁, hIc]
    simp [abs_le]
  · -- a box holding `(1, 1)` and `(-1, -1)` holds `(1, -1)`, which is not on the diagonal
    rintro ⟨I, hI⟩
    have hp : (fun _ => (1 : ℝ) : Vec ℝ 2) ∈ zB.construct :=
      (hmem _).mpr ⟨fun i => by simp, 1, by simp, fun i => rfl⟩
    have hm : (fun _ => (-1 : ℝ) : Vec ℝ 2) ∈ zB.construct :=
      (hmem _).mpr ⟨fun i => by simp, -1, by simp, fun i => rfl⟩
    rw [hI, hIc] at hp hm
    have hq : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1 : Vec ℝ 2) ∈ I.construct := by
      rw [hIc, Fin.forall_fin_two]
      exact ⟨⟨(hp 0).1, (hp 0).2⟩, (hm 1).1, (hm 1).2⟩
    rw [← hI, hmem] at hq
    obtain ⟨t, -, ht⟩ := hq.2
    have h0 := ht 0
    have h1 := ht 1
    simp at h0 h1
    linarith


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
