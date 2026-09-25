import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter

/-!
# `Zonotope.mtimesIntervalMat` over-approximates every matrix in the box

`mtimes` at the interval's own `centreMat` already covers what any single
matrix `A` in the box does through its centre; what `A` does beyond that is
`(A - centreMat) *ᵥ x`, a matrix known only to within `matResidual` acting on a
point known only to within `absBoundError`, which is exactly the box
`Interval.mtimesIntervalMat` already encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A` splits into its action through the centre matrix and the leftover. -/
theorem Zonotope.aux_mulVec_split (IM : Interval (Mat 𝕋 m n)) (A : Mat ℝ m n) (x : Vec ℝ n) :
    A *ᵥ x = toRealMat (Interval.centreMat IM) *ᵥ x
      + (fun i j => A i j - toReal (Interval.centreMat IM i j)) *ᵥ x := by -- --- PROOF ---
  rw [← Matrix.add_mulVec]
  congr 1
  funext i j
  show A i j = toReal (Interval.centreMat IM i j) + (A i j - toReal (Interval.centreMat IM i j))
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope 𝕋 n) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' Z.construct) ⊆
      (Zonotope.mtimesIntervalMat IM Z).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  -- the centre matrix acts through `mtimes`, already proven sound
  obtain ⟨t₀, ht₀, e₀, he₀, hsum⟩ := Zonotope.mtimes_outer (Interval.centreMat IM) Z
    ⟨x, hxmem, rfl⟩
  -- `A` known only to within `matResidual` of the centre matrix
  have hAsub : (fun i j => A i j - toReal (Interval.centreMat IM i j)) ∈
      (Interval.matResidual IM.inf IM.sup (Interval.centreMat IM)).construct :=
    Interval.sub_mem_matResidual fun i j => hA (i, j)
  -- `x` known only to within `absBoundError`
  have hxbox : x ∈ (Interval.symmetric fun j => Zonotope.absBoundError Z j).construct :=
    fun j => by
      have hb := abs_le.mp (Zonotope.abs_le_absBoundError hxmem j)
      show toReal (neg (Zonotope.absBoundError Z j)) ≤ x j
        ∧ x j ≤ toReal (Zonotope.absBoundError Z j)
      rw [toReal_neg]
      exact hb
  -- the leftover is what `mtimesIntervalMat` (box times box) already encloses
  have hDmem : (fun i j => A i j - toReal (Interval.centreMat IM i j)) *ᵥ x ∈
      (Interval.mtimesIntervalMat (Interval.matResidual IM.inf IM.sup (Interval.centreMat IM))
        (Interval.symmetric fun j => Zonotope.absBoundError Z j)).construct :=
    Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hAsub ⟨x, hxbox, rfl⟩)
  refine ⟨t₀, ht₀,
    e₀ + (fun i j => A i j - toReal (Interval.centreMat IM i j)) *ᵥ x,
    Interval.plus_outer _ _ (Set.add_mem_add he₀ hDmem), ?_⟩
  show t₀ + (e₀ + (fun i j => A i j - toReal (Interval.centreMat IM i j)) *ᵥ x) = A *ᵥ x
  have hsum' : t₀ + e₀ = toRealMat (Interval.centreMat IM) *ᵥ x := hsum
  rw [← add_assoc, hsum', Zonotope.aux_mulVec_split IM A x]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
