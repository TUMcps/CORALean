module

public import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormBallEq

@[expose] public section

/-!
# Zonotope containment as a norm bound

`[1, Eq. 18]`, the problem `ZC`: for a non-degenerate circumbody,
`Z₁ ⊆ Z₂` iff every `p ∈ Z₁` has `‖p - c₂‖_{Z₂} ≤ 1`. `[1, Cor. 1]` pointwise.

## Inputs
* `Z₁` – zonotope tested
* `Z₂` – containing zonotope

## Hypotheses
* `hG` – generator map of `Z₂` surjective

## Conclusion
* containment holds iff every zonotope norm is at most one

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.subset_iff_forall_zonotopeNorm_le (Z₁ Z₂ : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z₂.genMap) :
    Z₁.construct ⊆ Z₂.construct ↔ ∀ p ∈ Z₁.construct, Z₂.zonotopeNorm (p - Z₂.c) ≤ 1 := by
  rw [← (Z₂.zonotopeNorm_ball_eq hG).1]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
