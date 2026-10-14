module

public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachSupportFloat
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotLe
public import CORALean.ContSet.Zonotope.Float.Theorems.LowerDotLe

@[expose] public section

/-!
# The float support value is an upper bound

`minBackReachSupportFloat`, [1, Alg. 1] lines 12-13, is `ρ(R̂^∃) - ρ(Ẑ_{U₀}, -N_(j,·))` rounded so
it comes out *above* the real difference: the first term through `ConZonotope.boundDot`, an upper
bound on the support of the step's set, the second through `Zonotope.lowerDot`, which some point
`w` of `Ẑ_{U₀}` meets or exceeds with `-N_(j,·) w`. So for every `x` of the step's set `N_(j,·) x
+ N_(j,·) w` is at most the float value, which is what eq. (44) asks of `p_(j)` as an upper bound:
`N_(j,·) x - ρ(Ẑ_{U₀}, -N_(j,·)) ≤ N_(j,·) x + N_(j,·) w`. Needs the error box of `Ẑ_{U₀}` to be
non-empty, a property of the stored bounds the caller states.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.minBackReachSupportFloat_ge (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope 𝕋 (Vec 𝕋 n)) (W₀ U₀ : Zonotope (Vec 𝕋 n)) (Zw : 𝕋 → Zonotope (Vec 𝕋 n))
    (N : Mat 𝕋 q n)
    (t₀ Δt : 𝕋) (η ν k : ℕ) (j : Fin q)
    (hE : ∀ i, toReal ((sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.I_error.inf i)
      ≤ toReal ((sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.I_error.sup i)) :
    ∃ w ∈ (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.construct,
      ∀ x ∈ (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).R.construct,
        (toRealMat N *ᵥ x) j + (toRealMat N *ᵥ w) j
          ≤ toReal (sys.minBackReachSupportFloat CZ W₀ U₀ Zw N t₀ Δt η ν k j) := by -- --- PROOF ---
  set s := sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k
  obtain ⟨w, hw, hlow⟩ := Zonotope.lowerDot_le s.ZU₀ (fun i => neg (N j i)) hE
  refine ⟨w, hw, fun x hx => ?_⟩
  have hR := s.R.boundDot_le (c := rowLin N j) (N j) (fun _ => rfl) x hx
  have hsub := sub_le_subUp (s.R.boundDot (c := rowLin N j) (N j) fun _ => rfl).val
    (s.ZU₀.lowerDot fun i => neg (N j i))
  have hneg : ∑ i, toReal (neg (N j i)) * w i = -(toRealMat N *ᵥ w) j := by
    show _ = -∑ i, toReal (N j i) * w i
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [toReal_neg]; ring
  rw [hneg] at hlow
  unfold LinearSys.minBackReachSupportFloat
  have hR' : (toRealMat N *ᵥ x) j
      ≤ toReal (s.R.boundDot (c := rowLin N j) (N j) fun _ => rfl).val := hR
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
