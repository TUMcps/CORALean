module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.correctedStep`

The state-bounding zonotope of [1, Prop. 2], one step of the set-membership estimator for the
system `x₊ = A x + B u + w`, `y = C x + v` with `w ∈ ⟨0, D_w⟩`, `v ∈ ⟨0, D_v⟩` [1, Eq. 12]: from
`X = ⟨c, H⟩`, the input `u`, the measurement `y₊` and the correction matrix `Λ`,
`c₊ = (I - ΛC)(A c + B u) + Λ y₊` and `H₊ = [(I - ΛC) A H  (I - ΛC) D_w  Λ D_v]`. It is the case
`T = I`, `N = 0` of `Zonotope.intersectDescriptor`, without that case's block of `n_v` zero
generators `(I - ΛC) N F`. `Λ` is any matrix; the enclosure holds for each.

## References

* [1] Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". IEEE Conference on Decision and Control (CDC),
      pp. 668-673, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.correctedStep (Λ : Mat ℝ n ny) (A : Mat ℝ n n) (B : Mat ℝ n nu) (Dw : Mat ℝ n nw)
    (C : Mat ℝ ny n) (Dv : Mat ℝ ny nv) (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  let K : Mat ℝ n n := 1 - Λ * C                                             -- I - ΛC
  { h := X.h + nw + nv
    c := K *ᵥ (A *ᵥ X.c + B *ᵥ u) + Λ *ᵥ y                                  -- Prop. 2
    G := Fin.append (Fin.append (fun j => K *ᵥ (A *ᵥ X.G j))                -- (I - ΛC) A H
      (fun j i => (K * Dw) i j))                                           -- (I - ΛC) D_w
      (fun j i => (Λ * Dv) i j) }                                          -- Λ D_v

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
