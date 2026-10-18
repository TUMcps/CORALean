module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox

@[expose] public section

/-!
# The computed run reaches no further than the exact set plus its own error

`reach_outer` run backwards, and the inclusion an inner approximation needs:
the computed set is inside the exact one *plus* `reachError`, so subtracting
`reachError` off it lands back inside `reachSet`.

The induction is the whole argument. `plus_exact` and `mtimes_exact` say a step
loses nothing until it reduces, `reduce_subset_add_box` bounds what reducing
costs, and the previous step's error rides through the step's own `A` — which
is why `reachError` multiplies it rather than carrying it unchanged.

At `k = 0` the run is `R₀` itself and the error is the origin.

Not stated over `Reduce`: the class gives only `construct s ⊆ construct
(reduce s o)`, which bounds nothing in this direction.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reverse of `reach_outer`: what a run computes stays inside the exact
reachable set widened by the error that run accumulated. -/
theorem LinearSysDT.reach_subset_reachSet_add_error (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : -- --- STMT ---
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct ⊆
      sys.reachSet (S := 𝒵) R₀ U k
        + (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the error is the origin, and every point of `R₀` is itself plus `0`
    intro x hx
    have h := Set.add_mem_add hx (Zonotope.mem_ofPoint (0 : Vec ℝ n))
    rwa [add_zero] at h
  | succ k ih =>
    set Rk := sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ with hRk
    set W := (Zonotope.mtimes sys.A Rk).plus U with hW
    have hunfold : sys.reach (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩ = Zonotope.reduce W o := rfl
    have herr : sys.reachError ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = (Zonotope.mtimes sys.A (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus
            (Zonotope.reduceBox W o) :=
      rfl
    rw [hunfold, herr, ← Zonotope.plus_exact]
    intro x hx
    -- the step's own box comes off first, then `plus` and `mtimes` split exactly
    obtain ⟨w, hw, b, hb, rfl⟩ := Zonotope.reduce_subset_add_box W o hx
    rw [hW, ← Zonotope.plus_exact, ← Zonotope.mtimes_exact] at hw
    obtain ⟨_, ⟨r, hr, rfl⟩, u, hu, rfl⟩ := hw
    obtain ⟨y, hy, e, he, rfl⟩ := ih hr
    -- the exact part and the error part, each carried through this step's `A`
    refine ⟨sys.A *ᵥ y + u, ⟨sys.A *ᵥ y, ⟨y, hy, ?_⟩, u, hu, rfl⟩,
      sys.A *ᵥ e + b, ⟨sys.A *ᵥ e, ?_, b, hb, rfl⟩, ?_⟩
    · rw [Scalar.toRealMat_real]; rfl
    · rw [← Zonotope.mtimes_exact]; exact ⟨e, he, rfl⟩
    · show sys.A *ᵥ y + u + (sys.A *ᵥ e + b) = sys.A *ᵥ (y + e) + u + b
      rw [Matrix.mulVec_add]
      abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
