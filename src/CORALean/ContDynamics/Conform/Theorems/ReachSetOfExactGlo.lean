module

public import CORALean.ContDynamics.Conform.Definitions.Glo
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# [1, Thm. 1]: (7) is the exact reachable set of the GLO approximation

Linearized along the reference `x̄₀ = x∗ + c_x`, `ūᵢ = u∗ᵢ + c_u` (8), the GLO
approximation reaches exactly `Ȳ` of (7) from `x∗ ⊕ X₀` under inputs in `u∗ᵢ ⊕ Uᵢ`
— an equality, as the paper argues after the proof: every uncertain variable enters
`τ̄` once, so no dependency is lost, and the inputs are chosen independently per step.

## Inputs
* `yb` – reference output
* `Cb` – state-to-output matrix
* `Db` – input-to-output matrices
* `xs` – nominal initial state
* `cx` – initial center offset
* `X0` – initial uncertainty set
* `us` – nominal inputs
* `cu` – input center offset
* `U` – input uncertainty sets

## Hypotheses
* none

## Conclusion
* the reachable set of the approximation equals its generator-form set

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], (7): the GLO approximation's reachable set is `Ȳ`. -/
theorem Conform.reachSetOfExact_glo (yb : Vec ℝ q) (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p)
    (xs cx : Vec ℝ n) (X0 : Set (Vec ℝ n)) (us : Fin (k + 1) → Vec ℝ p) (cu : Vec ℝ p)
    (U : Fin (k + 1) → Set (Vec ℝ p)) : -- --- CONCL ---
    Conform.reachSetOfExact (Conform.glo yb Cb Db (xs + cx) fun i => us i + cu) xs X0 us U
      = Conform.gloSet yb Cb Db cx X0 cu U := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x0, hx0, u, hu, rfl⟩
    rw [Set.singleton_add] at hx0
    obtain ⟨xt, hxt, rfl⟩ := hx0
    have hu' : ∀ i, ∃ ut ∈ U i, us i + ut = u i := fun i => by
      have := hu i
      rwa [Set.singleton_add] at this
    choose ut hut hueq using hu'
    -- the deviations from the reference are `-c_x + x̃` and `-c_u + ũᵢ`
    have heq : Conform.glo yb Cb Db (xs + cx) (fun i => us i + cu) (xs + xt) u
        = yb + Cb *ᵥ (-cx + xt) + ∑ i, Db i *ᵥ (-cu + ut i) := by
      simp only [Conform.glo, ← hueq]
      congr 1
      · congr 2
        abel
      · exact Finset.sum_congr rfl fun i _ => by congr 1; abel
    rw [heq]
    exact Set.add_mem_add (Set.add_mem_add rfl ⟨_, ⟨-cx, rfl, xt, hxt, rfl⟩, rfl⟩)
      ((Set.mem_fintype_sum _ _).mpr ⟨_, fun i => ⟨_, ⟨-cu, rfl, ut i, hut i, rfl⟩, rfl⟩, rfl⟩)
  · -- a point of `Ȳ` is reached from `x∗ + x̃` under the inputs `u∗ᵢ + ũᵢ`
    rintro ⟨_, ⟨yb', hyb, _, ⟨_, ⟨cx', hcx, xt, hxt, rfl⟩, rfl⟩, rfl⟩, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hyb hcx
    subst hyb hcx
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).mp hb
    have hg' : ∀ i, ∃ ut ∈ U i, Db i *ᵥ (-cu + ut) = g i := fun i => by
      obtain ⟨_, ⟨cu', hcu, ut, hut, rfl⟩, hgi⟩ := hg i
      rw [Set.mem_singleton_iff] at hcu
      subst hcu
      exact ⟨ut, hut, hgi⟩
    choose ut hut hgeq using hg'
    refine ⟨xs + xt, ⟨xs, rfl, xt, hxt, rfl⟩, fun i => us i + ut i,
      fun i => ⟨us i, rfl, ut i, hut i, rfl⟩, ?_⟩
    simp only [Conform.glo, ← hgeq]
    congr 1
    · congr 2
      abel
    · exact Finset.sum_congr rfl fun i _ => by congr 1; abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
