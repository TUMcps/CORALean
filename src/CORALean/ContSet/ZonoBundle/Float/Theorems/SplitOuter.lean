import CORALean.ContSet.ZonoBundle.Float.Operations.Split
import CORALean.ContSet.ZonoBundle.Float.Theorems.IntersectionExact
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.SplitOuter

/-!
# The halves of a float bundle split cover the bundle

Whenever the bundle lies in the image of the box `B` under the directions `Λ` (over ℝ: `B`
encloses `Λ⁻¹ Z_∩`), every point of it lies in the float parallelotope (`mtimes_outer` after
`zonotope_contains`), so in one of its float halves (`split_outer`), and the halves are the
bundle cut with them (`intersection_exact`). Outer only: the exact layer's halves cover the
bundle exactly, the float ones also hold the rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.split_outer (Λ : Mat 𝕋 n n) (B : Interval (Vec 𝕋 n)) (j : Fin n)
    (zB : ZonoBundle 𝕋 n) (hB : zB.construct ⊆ (toRealMat Λ *ᵥ ·) '' B.construct) :
    zB.construct ⊆
      (zB.split Λ B j).1.construct ∪ (zB.split Λ B j).2.construct := by -- --- PROOF ---
  intro x hx
  -- the point lies in the float parallelotope
  have hΨ : x ∈ (Zonotope.mtimes Λ B.zonotope).construct := by
    obtain ⟨y, hy, rfl⟩ := hB hx
    exact Zonotope.mtimes_outer Λ B.zonotope ⟨y, Interval.zonotope_contains B hy, rfl⟩
  -- a one-member bundle denotes its member
  have h1 : ∀ Z : Zonotope 𝕋 n,
      ZonoBundle.construct (⟨1, fun _ => Z⟩ : ZonoBundle 𝕋 n) = Z.construct :=
    fun Z => Set.iInter_const (ι := Fin 1) Z.construct
  -- so in one of the two halves, and the bundle half is the bundle cut with it
  rcases Zonotope.split_outer (Zonotope.mtimes Λ B.zonotope) j hΨ with h | h
  · left
    show x ∈ (zB.intersection _).construct
    rw [ZonoBundle.intersection_exact, h1]
    exact ⟨hx, h⟩
  · right
    show x ∈ (zB.intersection _).construct
    rw [ZonoBundle.intersection_exact, h1]
    exact ⟨hx, h⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
