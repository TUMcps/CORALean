module

public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachSupportFloat
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotLe
public import CORALean.ContSet.Zonotope.Float.Operations.LowerDot
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The float support value is an upper bound

`minBackReachSupportFloat`, [1, Alg. 2] lines 12-13, is `ρ(R̂^∃) - ρ(Ẑ_{U₀}, -N_(j,·))` rounded so
it comes out *above* the real difference: the first term through `ConZonotope.boundDot`, an upper
bound on the support of the step's set, the second through `Zonotope.lowerDot`, which some point
`w` of `Ẑ_{U₀}` meets or exceeds with `-N_(j,·) w`. So for every `x` of the step's set `N_(j,·) x
+ N_(j,·) w` is at most the float value, which is what eq. (46) asks of `p_(j)` as an upper bound:
`N_(j,·) x - ρ(Ẑ_{U₀}, -N_(j,·)) ≤ N_(j,·) x + N_(j,·) w`. Needs the error box of `Ẑ_{U₀}` to be
non-empty, a property of the stored bounds the caller states.

## Inputs
* `sys` – linear system
* `CZ` – target constrained zonotope
* `W₀` – initial disturbance float zonotope
* `U₀` – initial input float zonotope
* `Zw` – center trajectory contribution
* `N` – direction matrix
* `t₀` – float start time
* `Δt` – float step length
* `η` – Taylor order
* `ν` – number of squarings
* `k` – step index
* `j` – direction index

## Hypotheses
* `hE` – input error box is ordered

## Conclusion
* the float support value bounds the exact one from above

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Float
section
open Pointwise InflatedContSet
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Zonotope.lowerDot` is attained from below. -/
private theorem Zonotope.aux_lowerDot_le (Z : Zonotope (Vec 𝕋 n)) (a : Vec 𝕋 n)
    (hE : ∀ i, toReal (Z.I_error.inf i) ≤ toReal (Z.I_error.sup i)) : -- --- CONCL ---
    ∃ x ∈ Z.construct, toReal (Z.lowerDot a) ≤ ∑ i, toReal (a i) * x i := by -- --- PROOF ---
  -- the generator signs and the box corner the support formula names
  set s : Fin Z.h → ℝ := fun j => ∑ i, toReal (a i) * toReal (Z.G j i) with hs
  set β : Vec ℝ Z.h := fun j => if 0 ≤ s j then 1 else -1 with hβ
  set e : Vec ℝ n := fun i =>
    if toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    then toReal (Z.I_error.inf i) else toReal (Z.I_error.sup i) with he
  -- the signs are admissible coefficients, and the corner is in the box
  have hβ1 : ∀ j, |β j| ≤ 1 := fun j => by
    by_cases h : 0 ≤ s j <;> simp [hβ, h]
  have hsβ : ∀ j, s j * β j = |s j| := fun j => by
    by_cases h : 0 ≤ s j
    · simp [hβ, h, abs_of_nonneg h]
    · simp [hβ, h, abs_of_neg (not_le.mp h)]
  have hemem : e ∈ Z.I_error.construct := fun i => by
    show toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i)
    by_cases h : toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    · rw [show e i = toReal (Z.I_error.inf i) from if_pos h]; exact ⟨le_rfl, hE i⟩
    · rw [show e i = toReal (Z.I_error.sup i) from if_neg h]; exact ⟨hE i, le_rfl⟩
  set z : Vec ℝ n := fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * β j with hz
  refine ⟨z + e, ⟨z, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ1, fun i => rfl⟩, e, hemem, rfl⟩, ?_⟩
  -- the value at that point
  have hval : ∑ i, toReal (a i) * (z + e) i
      = ∑ i, toReal (a i) * toReal (Z.c i) + ∑ j, |s j| + ∑ i, toReal (a i) * e i := by
    -- the nominal part: the signs make each generator contribute its absolute value
    have h1 : ∑ i, toReal (a i) * z i
        = ∑ i, toReal (a i) * toReal (Z.c i) + ∑ j, |s j| := by
      calc ∑ i, toReal (a i) * z i
          = ∑ i, toReal (a i) * toReal (Z.c i)
            + ∑ i, ∑ j, toReal (a i) * toReal (Z.G j i) * β j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hz, mul_add, Finset.mul_sum]
            exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
        _ = _ := by
            rw [Finset.sum_comm]
            refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
            rw [← hsβ j, hs]
            simp only [Finset.sum_mul]
    calc ∑ i, toReal (a i) * (z + e) i
        = ∑ i, toReal (a i) * z i + ∑ i, toReal (a i) * e i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by simp [mul_add]
      _ = _ := by rw [h1]
  rw [hval]
  -- each term of `lowerDot` below its exact value
  have hc : toReal (dotDown a Z.c) ≤ ∑ i, toReal (a i) * toReal (Z.c i) := dotDown_le a Z.c
  -- the generators: `max(0, lo, -hi)` is below `|aᵀGⱼ|`
  have hg : toReal (sumDown fun j => maximum FloatOps.zero
      (maximum (dotDown a fun i => Z.G j i) (neg (dotUp a fun i => Z.G j i)))) ≤ ∑ j, |s j| := by
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => ?_)
    rw [toReal_maximum, toReal_maximum, toReal_neg, toReal_zero]
    have hlo := dotDown_le a fun i => Z.G j i
    have hhi := le_dotUp a fun i => Z.G j i
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans hlo (le_abs_self _)
    · exact le_trans (neg_le_neg hhi) (neg_le_abs _)
  -- the box: the smaller end of each coordinate
  have hb : toReal (sumDown fun i => minimum (mulDown (a i) (Z.I_error.inf i))
      (mulDown (a i) (Z.I_error.sup i))) ≤ ∑ i, toReal (a i) * e i := by
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_)
    rw [toReal_minimum]
    by_cases h : toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    · simp only [he, if_pos h]
      exact le_trans (min_le_left _ _) (mulDown_le_mul _ _)
    · simp only [he, if_neg h]
      exact le_trans (min_le_right _ _) (mulDown_le_mul _ _)
  unfold Zonotope.lowerDot
  refine le_trans (addDown_le_add _ _) ?_
  refine add_le_add (le_trans (addDown_le_add _ _) (add_le_add hc hg)) hb

end
end Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.minBackReachSupportFloat_ge (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope 𝕋 (Vec 𝕋 n)) (W₀ U₀ : Zonotope (Vec 𝕋 n)) (Zw : 𝕋 → Zonotope (Vec 𝕋 n))
    (N : Mat 𝕋 q n)
    (t₀ Δt : 𝕋) (η ν k : ℕ) (j : Fin q)
    (hE : ∀ i, toReal ((sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.I_error.inf i)
      ≤ toReal ((sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.I_error.sup i))
    : -- --- CONCL ---
    ∃ w ∈ (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).ZU₀.construct,
      ∀ x ∈ (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).R.construct,
        (toRealMat N *ᵥ x) j + (toRealMat N *ᵥ w) j
          ≤ toReal (sys.minBackReachSupportFloat CZ W₀ U₀ Zw N t₀ Δt η ν k j) := by -- --- PROOF ---
  set s := sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k
  obtain ⟨w, hw, hlow⟩ := Zonotope.aux_lowerDot_le s.ZU₀ (-(N j)) hE
  refine ⟨w, hw, fun x hx => ?_⟩
  have hR := s.R.boundDot_le (c := Real.HPolytope.rowLin (toRealMat N) j) (N j) (fun _ => rfl) x hx
  have hsub := sub_le_subUp (s.R.boundDot (c := Real.HPolytope.rowLin (toRealMat N) j) (N j) fun _
      => rfl).val
    (s.ZU₀.lowerDot (-(N j)))
  have hneg : ∑ i, toReal ((-N j) i) * w i = -(toRealMat N *ᵥ w) j := by
    show _ = -∑ i, toReal (N j i) * w i
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, toReal_neg']; ring
  rw [hneg] at hlow
  unfold LinearSys.minBackReachSupportFloat
  have hR' : (toRealMat N *ᵥ x) j
      ≤ toReal (s.R.boundDot (c := Real.HPolytope.rowLin (toRealMat N) j) (N j) fun _ => rfl).val
          := hR
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
