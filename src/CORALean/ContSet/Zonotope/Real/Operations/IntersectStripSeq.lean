import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip

/-!
# `Zonotope.intersectStripSeq`

The strips `|C x - y| ≤ φ` taken one at a time, [1, Eq. 3]: the zonotope is met with the first
strip by [1, Prop. 6] at the gain `λ₁`, the result with the second at `λ₂`, and so on. Step `i`
reads `p̂_{k/i} = p̂_{k/i-1} + λ_i (y_i - c_iᵀ p̂_{k/i-1})` and
`Ĥ_{k/i} = [κ_i Ĥ_{k/i-1}  φ_i λ_i]` with `κ_i = I - λ_i c_iᵀ`, which is `intersectStrip` at the
one strip `i` and the one gain column `λ_i`. CORA's `priv_observe_intersectionMethod_I` is this.

The gain of strip `i` is column `i` of `Λ Z`, `Z` the zonotope it meets. A gain fixed offline, as
[1, Eq. 9] computes it, is a constant `Λ`; CORA's online methods (`'alamo-FRad'`,
`'alamo-volume'`) compute it from `Z`. Nothing here depends on which: the enclosure
(`intersectStripSeq_outer`) holds for every gain.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The strips of `C`, `φ`, `y` met one after the other, strip `i` at the gain column `i` of
`Λ` evaluated at the zonotope it meets. -/
def Zonotope.intersectStripSeq (C : Mat ℝ p n) (φ y : Vec ℝ p)
    (Λ : Zonotope (Vec ℝ n) → Mat ℝ n p) (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  (List.finRange p).foldl
    (fun X i =>                                                  -- X̂_{k/i} from X̂_{k/i-1}
      let c_i : Mat ℝ 1 n := Matrix.of fun _ => C i              -- the row c_iᵀ
      let l_i : Mat ℝ n 1 := Matrix.of fun r _ => Λ X r i        -- the gain λ_i
      X.intersectStrip c_i (fun _ => φ i) (fun _ => y i) l_i)
    Z                                                            -- X̂_{k/0}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
