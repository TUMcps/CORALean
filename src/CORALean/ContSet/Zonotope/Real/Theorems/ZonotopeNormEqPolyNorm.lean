module

public import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormBallEq
public import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormIsAsymmNorm
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct

@[expose] public section

/-!
# The zonotope norm is the polyhedral norm of the zonotope

`[1, Cor. 2]`: for a non-degenerate `Z` centered at the origin, `‖p‖_Z = S_Z(p)` for any
halfspace representation `{H x ≤ h}` of `Z` with every `hᵢ ≠ 0`. Since `0 ∈ Z`, each
`hᵢ > 0`; then both functions are positively homogeneous, nonnegative, and have the unit
ball `Z` (`zonotopeNorm_ball_eq`, `polyNorm_isAsymmNorm`), so `ν(p) ≤ t ↔ S_Z(p) ≤ t` for
every `t > 0`, and two nonnegative numbers with that property agree.

## Inputs
* `Z` – zonotope
* `H` – facet matrix
* `h` – facet offsets
* `x` – vector

## Hypotheses
* `hc` – center at the origin
* `hG` – generator map surjective
* `hrep` – facets describe `Z`
* `hne` – offsets nonzero

## Conclusion
* the zonotope norm equals the polytope norm

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_eq_polyNorm (Z : Zonotope (Vec ℝ n)) (hc : Z.c = 0)
    (hG : Function.Surjective Z.genMap) {H : Mat ℝ s n} {h : Vec ℝ s}
    (hrep : (HPolytope.ineqs H h).construct = Z.construct) (hne : ∀ i, h i ≠ 0)
    (x : Vec ℝ n) : -- --- CONCL ---
    Z.zonotopeNorm x = HPolytope.polyNorm H h x := by -- --- PROOF ---
  obtain ⟨hball, -⟩ := Z.zonotopeNorm_ball_eq hG
  -- `0 ∈ Z` makes every right-hand side positive
  have hpos : ∀ i, 0 < h i := fun i => by
    have h0 : (0 : Vec ℝ n) ∈ (HPolytope.ineqs H h).construct := by
      rw [hrep, ← hc]; exact Z.center_mem_construct
    have := HPolytope.mem_ineqs_iff.mp h0 i
    simp only [mulVec_zero, Pi.zero_apply] at this
    exact lt_of_le_of_ne this (hne i).symm
  obtain ⟨-, hhom, hrest⟩ := (HPolytope.polyNorm_isAsymmNorm (H := H) (h := h))
  have hunit := (hrest hpos).1
  -- both are below `t > 0` exactly when `t⁻¹ x ∈ Z`
  have hiff : ∀ t : ℝ, 0 < t → (Z.zonotopeNorm x ≤ t ↔ HPolytope.polyNorm H h x ≤ t) := by
    intro t ht
    have e₁ : Z.zonotopeNorm x ≤ t ↔ Z.zonotopeNorm (t⁻¹ • x) ≤ 1 := by
      rw [show Z.zonotopeNorm (t⁻¹ • x) = |t⁻¹| * Z.zonotopeNorm x from
        coeffNorm_smul _ (hG x) _, abs_of_pos (inv_pos.mpr ht), inv_mul_le_iff₀ ht, mul_one]
    have e₂ : HPolytope.polyNorm H h x ≤ t ↔ HPolytope.polyNorm H h (t⁻¹ • x) ≤ 1 := by
      rw [hhom _ _ (inv_pos.mpr ht), inv_mul_le_iff₀ ht, mul_one]
    have e₃ : Z.zonotopeNorm (t⁻¹ • x) ≤ 1 ↔ t⁻¹ • x ∈ Z.construct := by
      rw [← hball, Set.mem_setOf_eq, hc, sub_zero]
    rw [e₁, e₂, e₃, hunit, hrep]
  have h0ν : 0 ≤ Z.zonotopeNorm x := coeffNorm_nonneg _ _
  have h0S : 0 ≤ HPolytope.polyNorm H h x := (HPolytope.polyNorm_le_iff.mp le_rfl).1
  -- two nonnegative numbers below the same positive bounds are equal
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
    (le_of_forall_pos_lt_add fun ε hε => ?_)
  · have := (hiff (HPolytope.polyNorm H h x + ε / 2) (by linarith)).mpr (by linarith)
    linarith
  · have := (hiff (Z.zonotopeNorm x + ε / 2) (by linarith)).mp (by linarith)
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
