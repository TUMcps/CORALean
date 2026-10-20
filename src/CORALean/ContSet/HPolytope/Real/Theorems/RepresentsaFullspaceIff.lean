module

public import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaFullspace
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `representsaFullspace` is exactly "the set is the whole space"

If every row is trivial the set is everything. Conversely, a row `aᵀx ≤ b` that holds at every
point has `a = 0` (else scale a point with `aᵀx ≠ 0` past `b`) and `b ≥ 0` (at `0`), and an
equality row `aᵀx = be` that holds at every point has `be = 0` (at `0`) and so `a = 0`.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* `representsaFullspace` is exactly "the set is the whole space"
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.representsaFullspace_iff (P : HPolytope α) : -- --- CONCL ---
    P.representsaFullspace ↔ P.construct = Set.univ := by -- --- PROOF ---
  constructor
  · rintro ⟨h1, h2⟩
    refine Set.eq_univ_of_forall fun x => ⟨fun i => ?_, fun r => ?_⟩
    · rw [(h1 i).1]; simpa using (h1 i).2
    · rw [(h2 r).1, (h2 r).2]; simp
  · intro h
    have hx : ∀ x, x ∈ P.construct := fun x => h ▸ Set.mem_univ x
    have hb : ∀ i, 0 ≤ P.b i := fun i => by simpa using (hx 0).1 i
    -- scaling `x` so that the row exceeds its bound
    have hA : ∀ i, P.A i = 0 := fun i => by
      ext x
      by_contra hne
      have hne' : P.A i x ≠ 0 := hne
      have := (hx (((|P.b i| + 1) / P.A i x) • x)).1 i
      rw [LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ hne'] at this
      linarith [le_abs_self (P.b i)]
    have hbe : ∀ r, P.be r = 0 := fun r => by simpa using ((hx 0).2 r).symm
    refine ⟨fun i => ⟨hA i, hb i⟩, fun r => ⟨?_, hbe r⟩⟩
    ext x
    have h1 := (hx x).2 r
    rw [hbe r] at h1
    simpa using h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
