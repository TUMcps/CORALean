import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Float.Operations.MatMul
import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsMatOuter
import CORALean.ContSet.Zonotope.Real.Operations.MatMul
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter

/-!
# `Zonotope.matMul` over-approximates every product of two members

`(a + e)(b + f) = ab + (af + e(b + f))`. The nominal product `ab` lies in the exact
`Zonotope.matMul` (`matMul_outer`), whose centre and generators the directed products
bracket, entry by entry, as `dotDown_le`/`le_dotUp` state them; `af` and `e(b + f)` are
`Interval.matMul_outer` at the two boxes `matInterval_contains` supplies.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One exact product of stored matrices, between its two directed roundings. -/
theorem Zonotope.aux_matMul_bounds (A : Mat 𝕋 p q) (B : Mat 𝕋 q r) (i : Fin p) (j : Fin r) :
    toReal (matMulDown A B i j) ≤ matMulBilin (toRealMat A) (toRealMat B) i j
      ∧ matMulBilin (toRealMat A) (toRealMat B) i j ≤ toReal (matMulUp A B i j) := by
  rw [matMulBilin_apply, Matrix.mul_apply]
  exact ⟨dotDown_le (A i) (fun l => B l j), le_dotUp (A i) (fun l => B l j)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMul_outer (M : Zonotope (Mat 𝕋 p q)) (N : Zonotope (Mat 𝕋 q r)) :
    (⋃ A ∈ M.construct, (A * ·) '' N.construct)
      ⊆ (Zonotope.matMul M N).construct := by -- --- PROOF ---
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨_, ⟨a, ha, e, he, rfl⟩, _, ⟨b, hb, f, hf, rfl⟩, rfl⟩ := hy
  set Z := CORALean.Real.Zonotope.matMul M.nominal N.nominal
  have hab : a * b ∈ Z.construct :=
    CORALean.Real.Zonotope.matMul_outer _ _ (Set.mem_biUnion ha ⟨b, hb, rfl⟩)
  -- the first nominal part, boxed: it is the nominal part of `M` with a zero box
  have ha' : a ∈ ({ M with E := Interval.point fun _ _ => zero } :
      Zonotope (Mat 𝕋 p q)).matInterval.construct := by
    refine Zonotope.matInterval_contains _ ⟨a, ha, 0, ?_, add_zero a⟩
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩
  have hB : b + f ∈ N.matInterval.construct :=
    Zonotope.matInterval_contains N ⟨b, hb, f, hf, rfl⟩
  -- each generator block of `bilin`, bracketed by the same directed products
  have hG : ∀ k i j, toReal (Fin.append (Fin.append (fun i => matMulDown (M.G i) N.c)
        (fun j => matMulDown M.c (N.G j))) (fun k => matMulDown (M.G (finProdFinEquiv.symm k).1)
          (N.G (finProdFinEquiv.symm k).2)) k i j) ≤ Z.G k i j
      ∧ Z.G k i j ≤ toReal (Fin.append (Fin.append (fun i => matMulUp (M.G i) N.c)
        (fun j => matMulUp M.c (N.G j))) (fun k => matMulUp (M.G (finProdFinEquiv.symm k).1)
          (N.G (finProdFinEquiv.symm k).2)) k i j) := by
    intro k i j
    refine Fin.addCases (fun k' => Fin.addCases (fun l => ?_) (fun l => ?_) k') (fun l => ?_) k
      <;> simp only [Z, CORALean.Real.Zonotope.matMul, CORALean.Real.Zonotope.bilin,
        Zonotope.nominal, realImage_mat, Fin.append_left, Fin.append_right]
      <;> exact Zonotope.aux_matMul_bounds _ _ i j
  -- the nominal product rounded, the two error terms in the box
  have hmem : a * b + (a * f + e * (b + f)) ∈ (Zonotope.matMul M N).construct :=
    Zonotope.ofEntryBoundsMat_outer Z _ (fun i j => Zonotope.aux_matMul_bounds M.c N.c i j) hG
      ⟨a * b, hab, _, Interval.matPlus_outer _ _ (Interval.matMul_outer _ _ ha' hf)
        (Interval.matMul_outer _ _ he hB), rfl⟩
  have heq : (a + e) * (b + f) = a * b + (a * f + e * (b + f)) := by
    rw [Matrix.add_mul, Matrix.mul_add a b f, add_assoc]
  show (a + e) * (b + f) ∈ _
  rw [heq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
