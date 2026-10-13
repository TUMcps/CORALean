module

public import CORALean.ContSet.ContSet.Definitions.IntersectStrip

@[expose] public section

/-!
# The strips one at a time

The strips `|C x - y| ≤ φ` taken one at a time, [1, Eq. 3]: the set is met with the first
strip by [1, Prop. 6] at the gain `λ₁`, the result with the second at `λ₂`, and so on. Step `i`
reads `p̂_{k/i} = p̂_{k/i-1} + λ_i (y_i - c_iᵀ p̂_{k/i-1})` and
`Ĥ_{k/i} = [κ_i Ĥ_{k/i-1}  φ_i λ_i]` with `κ_i = I - λ_i c_iᵀ`, which is `intersectStrip` at the
one strip `i` and the one gain column `λ_i`. CORA's `priv_observe_intersectionMethod_I` is this.
Written once over `IntersectStrip`, so a float zonotope runs the same loop in rounded arithmetic.

The gain of strip `i` is column `i` of `Λ Z`, `Z` the set it meets. A gain fixed offline, as
[1, Eq. 9] computes it, is a constant `Λ`; CORA's online methods (`'alamo-FRad'`,
`'alamo-volume'`) compute it from `Z`. Nothing here depends on which: the enclosure
(`intersectStripSeq_outer`) holds for every gain.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The strips of `C`, `φ`, `y` met one after the other, strip `i` at the gain column `i` of
`Λ` evaluated at the set it meets. -/
def ContSet.intersectStripSeq (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : S n → Mat 𝕋 n p)
    (Z : S n) : S n :=
  (List.finRange p).foldl
    (fun X i =>                                                  -- X̂_{k/i} from X̂_{k/i-1}
      let c_i : Mat 𝕋 1 n := Matrix.of fun _ => C i              -- the row c_iᵀ
      let l_i : Mat 𝕋 n 1 := Matrix.of fun r _ => Λ X r i        -- the gain λ_i
      intersectStrip c_i (fun _ => φ i) (fun _ => y i) l_i X)
    Z                                                            -- X̂_{k/0}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
