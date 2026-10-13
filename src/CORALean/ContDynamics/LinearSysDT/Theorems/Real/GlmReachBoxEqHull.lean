module

public import CORALean.ContDynamics.LinearSysDT.Operations.GlmReachBox
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.GlmReachEq
public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalEqHull

@[expose] public section

/-!
# `glmReachBox` returns the interval hulls of the reachable sets

[1, Prop. 1]: for every `i ∈ {1, …, N}`, `Ω̄ᵢ` is the interval hull of `Ωᵢ`. The run of
[1, Alg. 2] is that of [1, Alg. 1] with each `Sᵢ` replaced by its box, because the box of
a zonotope sum is the sum of the boxes, [1, Eq. 3] at the representation; so `Ω̄ᵢ` is the
box of the zonotope `Ωᵢ` that `glmReach` returns, which is `Interval.hull` of its set
(`Zonotope.interval_eq_hull`), and that set is `Ωᵢ` (`LinearSysDT.glmReach_eq`).

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` passes of a loop that steps its state by `f` and appends `g` of the new state. -/
theorem LinearSysDT.aux_glmReachBox_foldl {α β : Type} (f : α → α) (g : α → β) (a : α)
    (k : ℕ) :
    (List.range k).foldl (fun (s : α × List β) (_ : ℕ) => (f s.1, s.2 ++ [g (f s.1)])) (a, [])
      = (f^[k] a, (List.range k).map fun i => g (f^[i + 1] a)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Function.iterate_succ_apply']

/-- The box of a zonotope sum is the sum of the boxes. -/
theorem LinearSysDT.aux_interval_plus (Z₁ Z₂ : Zonotope (Vec ℝ n)) :
    (Z₁.plus Z₂).interval = Z₁.interval.plus Z₂.interval := by -- --- PROOF ---
  -- the generator sum splits at the concatenation, stated at `plus`'s own count
  have hs : ∀ i : Fin n, ∑ j : Fin (Z₁.plus Z₂).h, |Entrywise.entry ((Z₁.plus Z₂).G j) i|
      = ∑ j, |Entrywise.entry (Z₁.G j) i| + ∑ j, |Entrywise.entry (Z₂.G j) i| := fun i => by
    have h := Fin.sum_univ_add fun j : Fin (Z₁.h + Z₂.h) =>
      |Entrywise.entry (Fin.append Z₁.G Z₂.G j) i|
    simp only [Fin.append_left, Fin.append_right] at h
    exact h
  have hc : (Z₁.plus Z₂).c = Z₁.c + Z₂.c := rfl
  simp only [Zonotope.interval, Interval.plus]
  congr 1 <;> refine Entrywise.ext fun i => ?_ <;>
    simp only [Entrywise.entry_ofEntry, Entrywise.entry_add, hs, hc] <;> ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `Ω̄ᵢ` is the interval hull of `Ωᵢ`, for every `i ∈ {1, …, N}`. -/
theorem LinearSysDT.glmReachBox_eq_hull (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n))
    (N : ℕ) :
    sys.glmReachBox Ω₀ U N = (List.range N).map fun i =>
      Interval.hull (sys.reachSet (S := 𝒵) Ω₀ U (i + 1)) := by -- --- PROOF ---
  set Φ := toRealMat sys.A
  set f₁ := fun (s : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) =>
    (s.1.mtimes Φ, s.2.1.plus s.2.2, s.2.2.mtimes Φ) with hf₁
  set f₂ := fun (s : Zonotope (Vec ℝ n) × Interval (Vec ℝ n) × Zonotope (Vec ℝ n)) =>
    (s.1.mtimes Φ, s.2.1.plus s.2.2.interval, s.2.2.mtimes Φ) with hf₂
  set a₁ := (Ω₀, Zonotope.ofPoint (0 : Vec ℝ n), U)
  set a₂ : Zonotope (Vec ℝ n) × Interval (Vec ℝ n) × Zonotope (Vec ℝ n) := (Ω₀, ⟨0, 0⟩, U)
  -- Alg. 2's state is Alg. 1's with `Sᵢ` boxed
  have hφ : ∀ k, f₂^[k] a₂ = ((f₁^[k] a₁).1, (f₁^[k] a₁).2.1.interval, (f₁^[k] a₁).2.2) := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero, id, a₁, a₂, Prod.mk.injEq, true_and, and_true]
      simp only [Zonotope.interval, Zonotope.ofPoint, Finset.univ_eq_empty, Finset.sum_empty,
        sub_zero, add_zero, Entrywise.entry_zero]
      rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp only [hf₁, hf₂]
      rw [LinearSysDT.aux_interval_plus]
  -- so Alg. 2 returns the boxes of what Alg. 1 returns
  have hbox : sys.glmReachBox Ω₀ U N = (sys.glmReach Ω₀ U N).map Zonotope.interval := by
    rw [LinearSysDT.glmReachBox, LinearSysDT.glmReach,
      congrArg Prod.snd (LinearSysDT.aux_glmReachBox_foldl f₂
        (fun s => s.1.interval.plus s.2.1) a₂ N),
      congrArg Prod.snd (LinearSysDT.aux_glmReachBox_foldl f₁ (fun s => s.1.plus s.2.1) a₁ N),
      List.map_map]
    refine List.map_congr_left fun i _ => ?_
    rw [hφ, Function.comp_apply, LinearSysDT.aux_interval_plus]
  -- each box is the hull of the exact set
  rw [hbox, show (Zonotope.interval : Zonotope (Vec ℝ n) → _)
      = Interval.hull ∘ Zonotope.construct from funext Zonotope.interval_eq_hull,
    ← List.map_map, LinearSysDT.glmReach_eq, List.map_map]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
