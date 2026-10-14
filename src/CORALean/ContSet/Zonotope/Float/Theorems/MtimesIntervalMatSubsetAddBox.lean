module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMatBox
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesSubsetAddBox
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesError
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `mtimesIntervalMat` reaches no further than one matrix of the box, plus a box

The upper side of `mtimesIntervalMat_outer`: for every `A` in `IM`, the float
`[M] Z` lies in `A Z ⊕ mtimesIntervalMatBox IM Z`. A point of `[M] Z` is `t + d
+ e'`, `t` in `mid(M) Z`'s nominal part, `d` on the diagonal generators and `e'`
in the error box. `mtimes_subset_add_box` writes `t` as `mid(M) x + g` for some
`x ∈ Z`, and `mid(M) x = A x - (A - mid(M)) x`: the perturbation of the true
matrix is what the symmetric part of the box covers, `|A - mid(M)| |x|`.

This is the per-step bound an inner approximation through `[e^{AΔt}]` needs:
with `A` the true exponential, the float step minus this box, cancelled by
Rådström's law (`minkowskiDiff_inner_of_outer`), lies in the exact image.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `Z`, nominal part and error box together, reaches no further than
`|c| + Σ|G| + |E|`, rounded up. -/
theorem Zonotope.aux_abs_le_construct {Z : Zonotope (Vec 𝕋 n)} {z e : Vec ℝ n}
    (hz : z ∈ nominalSet Z) (he : e ∈ Z.I_error.construct) (j : Fin n) :
    |z j| ≤ toReal (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)) ∧
      |z j + e j| ≤ toReal (addUp (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
        (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j)))) := by -- --- PROOF ---
  obtain ⟨β, hβ, hzβ⟩ := Zonotope.mem_nominalSet_iff.mp hz
  have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
    (fun _ _ => le_refl _) hβ j
  have hup := add_le_addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)
  rw [toReal_absolute] at hup
  -- the nominal part, as `mtimesIntervalMat_outer` bounds it
  have hzb : |z j| ≤ toReal (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)) := by
    rw [hzβ j]
    exact le_trans (le_trans (abs_add_le _ _) (by linarith)) hup
  -- the error box, by the larger magnitude of its bounds
  have hej : toReal (Z.I_error.inf j) ≤ e j ∧ e j ≤ toReal (Z.I_error.sup j) := he j
  have heb : |e j| ≤ toReal (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j))) :=
      by
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hej.1 hej.2
  exact ⟨hzb, le_trans (abs_add_le _ _) (le_trans (add_le_add hzb heb) (add_le_addUp _ _))⟩

/-- `∑ⱼ |Rᵢⱼ| |xⱼ|` stays below the rounded-up `∑ⱼ rᵢⱼ ξⱼ` once each factor does. -/
theorem Zonotope.aux_abs_mulVec_le {R : Mat ℝ m n} {x : Vec ℝ n} {r : Mat 𝕋 m n} {ξ : Vec 𝕋 n}
    (hr : ∀ i j, |R i j| ≤ toReal (r i j)) (hx : ∀ j, |x j| ≤ toReal (ξ j)) (i : Fin m) :
    |(R *ᵥ x) i| ≤ toReal (sumUp fun j => mulUp (r i j) (ξ j)) := by -- --- PROOF ---
  show |∑ j, R i j * x j| ≤ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  exact le_trans (mul_le_mul (hr i j) (hx j) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hr i j))) (mul_le_mulUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimesIntervalMat` reaches no further than the image of `Z.construct` under any `A` in
the box, widened by `mtimesIntervalMatBox`, provided `Z` brackets `0` in its own box. -/
theorem Zonotope.mtimesIntervalMat_subset_add_box (IM : Interval (Mat 𝕋 m n))
    (Z : Zonotope (Vec 𝕋 n)) (h : (0 : Vec ℝ n) ∈ Z.I_error.construct) {A : Mat ℝ m n}
    (hA : A ∈ IM.construct) :
    (Zonotope.mtimesIntervalMat IM Z).construct ⊆
      (A *ᵥ ·) '' Z.construct
        + (Zonotope.mtimesIntervalMatBox IM Z).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e', he', rfl⟩
  set C := Interval.centreMat IM with hC
  set Rs := Interval.matResidual IM.inf IM.sup C with hRs
  set R : Mat ℝ m n := fun i j => A i j - toReal (C i j) with hRdef
  set r : Mat 𝕋 m n := fun i j => maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))
    with hrdef
  set ν : Vec 𝕋 n := fun j => addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j) with hνdef
  set ξ : Vec 𝕋 n := fun j => addUp (ν j)
      (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j)))
    with hξdef
  set b : Vec 𝕋 m := fun i => sumUp fun j => mulUp (r i j) (ν j) with hbdef
  set a : Vec 𝕋 m := fun i => sumUp fun j => mulUp (r i j) (ξ j) with hadef
  -- `A` is within `matResidual` of the centre matrix, entry by entry
  have hR : R ∈ Rs.construct := Interval.sub_mem_matResidual fun i j => hA (i, j)
  have hr : ∀ i j, |R i j| ≤ toReal (r i j) := fun i j => by
    have hRij := hR (i, j)
    simp only [Entrywise.entry_mat] at hRij
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hRij.1 hRij.2
  -- the nominal point splits into `mid(M) Z`'s part and the diagonal generators' part
  obtain ⟨β, hβ, hyβ⟩ := Zonotope.mem_nominalSet_iff.mp hy
  set t : Vec ℝ m := fun i => toReal (mulVecDown C Z.c i)
    + ∑ l : Fin Z.h, toReal (mulVecDown C (Z.G l) i) * β (Fin.castAdd m l) with htdef
  set d : Vec ℝ m := fun i => toReal (b i) * β (Fin.natAdd Z.h i) with hddef
  have hytd : y = t + d := funext fun i => by
    rw [hyβ i]
    show toReal (mulVecDown C Z.c i) + ∑ j : Fin (Z.h + m),
        toReal (Fin.append (fun l => mulVecDown C (Z.G l)) (diagonalBlock b) j i) * β j = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    have hdiag : ∑ k, diagonal (toRealVec b) k i * β (Fin.natAdd Z.h k) = d i :=
      Real.Zonotope.sum_diagonal_mul' (toRealVec b) (fun k => β (Fin.natAdd Z.h k)) i
    rw [hdiag, ← add_assoc]
    rfl
  -- `t` is a point of `mid(M) Z`, whose error box holds `0`
  have ht : t ∈ (Zonotope.mtimes C Z).construct := by
    have hh : t + (0 : Vec ℝ m) ∈ (Zonotope.mtimes C Z).construct :=
      Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr
        ⟨fun l => β (Fin.castAdd m l), fun l => hβ _, fun _ => rfl⟩)
        (Zonotope.zero_mem_mtimes_error h)
    rwa [add_zero] at hh
  -- `mtimes_subset_add_box`: `t = mid(M) x + g₁` for some `x ∈ Z`
  obtain ⟨_, ⟨x, hx, rfl⟩, g₁, hg₁, htx⟩ := Zonotope.mtimes_subset_add_box C Z h ht
  obtain ⟨z, hz, e, he, hxze⟩ := hx
  have hxb : ∀ j, |x j| ≤ toReal (ξ j) := fun j => by
    rw [← hxze]
    exact (Zonotope.aux_abs_le_construct hz he j).2
  -- `b ≥ 0`, through the residual on the nominal point `z`
  have hb0 : ∀ i, 0 ≤ toReal (b i) := fun i =>
    le_trans (abs_nonneg _) (Zonotope.aux_abs_mulVec_le hr
      (fun j => (Zonotope.aux_abs_le_construct hz he j).1) i)
  -- `-(A - mid(M)) x + d` lies in the symmetric box
  have hsym : -(R *ᵥ x) + d ∈ (Interval.symmetric fun i => addUp (a i) (b i)).construct := by
    intro i
    have hRx := Zonotope.aux_abs_mulVec_le hr hxb i
    have hd : |d i| ≤ toReal (b i) := by
      show |toReal (b i) * β (Fin.natAdd Z.h i)| ≤ _
      rw [abs_mul, abs_of_nonneg (hb0 i)]
      exact mul_le_of_le_one_right (hb0 i) (hβ _)
    have hsum : |-(R *ᵥ x) i + d i| ≤ toReal (addUp (a i) (b i)) :=
      le_trans (abs_add_le _ _) (le_trans (by rw [abs_neg]; exact add_le_add hRx hd)
        (add_le_addUp _ _))
    rw [abs_le] at hsum
    exact ⟨by
        show toReal (neg (addUp (a i) (b i))) ≤ _
        rw [toReal_neg]
        exact hsum.1,
      hsum.2⟩
  refine ⟨A *ᵥ x, ⟨x, ⟨z, hz, e, he, hxze⟩, rfl⟩, g₁ + ((-(R *ᵥ x) + d) + e'),
    Interval.plus_outer _ _ (Set.add_mem_add hg₁
      (Interval.plus_outer _ _ (Set.add_mem_add hsym he'))), ?_⟩
  -- `A x = mid(M) x + (A - mid(M)) x`, and the rest regroups
  have hsplit : A *ᵥ x = toRealMat C *ᵥ x + R *ᵥ x := by
    rw [← Matrix.add_mulVec]
    congr 1
    funext i j
    show A i j = toReal (C i j) + (A i j - toReal (C i j))
    ring
  have htx' : t = toRealMat C *ᵥ x + g₁ := htx.symm
  show A *ᵥ x + (g₁ + ((-(R *ᵥ x) + d) + e')) = y + e'
  rw [hsplit, hytd, htx']
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
