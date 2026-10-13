module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaCapsuleCora
public import CORALean.ContSet.Capsule.Real.Theorems.OfPointMemIff

@[expose] public section

/-!
# CORA's `polyZonotope/representsa_(pZ, 'capsule')` errors on a point in dimension two or more

A polynomial zonotope without generators, `{c}` with `c ∈ ℝ²`, reaches the `&&` of l. 67 with a
true left operand and the `1 × 2` array `size(pZ.G,2) + size(pZ.GI) <= 1` on the right, which
MATLAB rejects. A point is a capsule, so the answer is `true`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polynomial zonotope `{c}`: no factor, no generator. -/
def PolyZonotope.aux_point (c : Vec ℝ 2) : PolyZonotope (Vec ℝ 2) :=
  ⟨0, 0, 0, c, Fin.elim0, fun k => k.elim0, Fin.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's test errors on `{c}`, which is the capsule `Capsule.ofPoint c`. -/
theorem PolyZonotope.representsa_capsule_cora_crash (c : Vec ℝ 2) :
    (PolyZonotope.aux_point c).representsaCapsuleCora = none ∧
      (PolyZonotope.aux_point c).construct = (Capsule.ofPoint c).construct := by
  refine ⟨by simp [PolyZonotope.representsaCapsuleCora, PolyZonotope.aux_point], ?_⟩
  ext x
  rw [Capsule.mem_ofPoint_iff]
  simp [PolyZonotope.construct, PolyZonotope.aux_point, eq_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
