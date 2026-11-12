module

public import CORALean.HybridDynamics.Operations.LocationGuardOrientFloat
public import CORALean.ContSet.HPolytope.Float.Theorems.InHalfspaceSound

@[expose] public section

/-!
# `Location.guardOrientFloat?` puts the invariant inside the oriented halfspace

If the oriented normal `c` and offset `d` are returned, every point of the invariant has
`c·y ≤ d` (`HPolytope.inHalfspace_sound`), and a point on the hyperplane `nv·z = γ` has `c·z = d`:
the normal is `nv` or its negation, with the offset.

## Inputs
* `ℓ` – location
* `nv` – normal of the guard hyperplane
* `γ` – offset of the guard hyperplane

## Hypotheses
none.

## Conclusion
* for the orientation `(c, d)` returned, the invariant is in `c·y ≤ d`, and the hyperplane is
  `c·z = d`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.guardOrientFloat?_sound
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (nv : Vec 𝕋 n)
    (γ : 𝕋) : -- --- CONCL ---
    ∀ cd ∈ ℓ.guardOrientFloat? nv γ, (∀ y ∈ ContSetLike.toSet ℓ.inv,
      toRealVec cd.1 ⬝ᵥ y ≤ toReal cd.2) ∧
      ∀ z : Vec ℝ n, z ⬝ᵥ toRealVec nv = toReal γ →
        toRealVec cd.1 ⬝ᵥ z = toReal cd.2 := by -- --- PROOF ---
  intro cd h
  unfold Location.guardOrientFloat? at h
  split_ifs at h with h1 h2
  · cases Option.mem_some_iff.mp h
    exact ⟨fun y hy => by rw [dotProduct_comm]; exact HPolytope.inHalfspace_sound h1 hy,
      fun z hz => by rw [dotProduct_comm]; exact hz⟩
  · cases Option.mem_some_iff.mp h
    refine ⟨fun y hy => ?_, fun z hz => ?_⟩
    · have := HPolytope.inHalfspace_sound h2 hy
      rw [dotProduct_comm]; simpa using this
    · have hn : ∀ a : 𝕋, toReal (-a) = -toReal a := fun a => toReal_neg a
      have : z ⬝ᵥ toRealVec (-nv) = -(z ⬝ᵥ toRealVec nv) := by
        simp only [dotProduct, toRealVec, Pi.neg_apply, hn, mul_neg, Finset.sum_neg_distrib]
      rw [dotProduct_comm, this, hz, hn]
  · exact absurd h (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
