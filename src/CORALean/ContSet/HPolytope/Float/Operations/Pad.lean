import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.Global.Block

/-!
# `HPolytope.padLeft`, `HPolytope.padRight`

The same constraints on a wider coefficient space, the new coordinates padded
with zeros so they answer to nothing. Exact: padding copies floats and computes
none.

This is the float counterpart of pulling a polytope back along a block
projection, and it is what a constrained zonotope's `plus` and interval-matrix
product need.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}

def HPolytope.padLeft (P : HPolytope 𝕋 n₁) (n₂ : ℕ) : HPolytope 𝕋 (n₁ + n₂) where
  m := P.m
  A := fun i => Fin.append (P.A i) fun _ => FloatOps.zero
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (P.Ae i) fun _ => FloatOps.zero
  be := P.be

-- the mirror, with the new coordinates padded in front
def HPolytope.padRight (n₁ : ℕ) (P : HPolytope 𝕋 n₂) : HPolytope 𝕋 (n₁ + n₂) where
  m := P.m
  A := fun i => Fin.append (fun _ => FloatOps.zero) (P.A i)
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (fun _ => FloatOps.zero) (P.Ae i)
  be := P.be

variable [SoundFloatArithmetic 𝕋]

-- a padded row reads only the block it came from, the zero columns dropping out
theorem HPolytope.mulVec_padLeft {m : ℕ} (M : Mat 𝕋 m n₁) (x : Vec ℝ (n₁ + n₂)) (i : Fin m) :
    (toRealMat (fun i' => Fin.append (M i') fun _ : Fin n₂ => FloatOps.zero) *ᵥ x) i
      = (toRealMat M *ᵥ blockLeft n₁ n₂ x) i := by
  show ∑ k : Fin (n₁ + n₂), toReal (Fin.append (M i) (fun _ => FloatOps.zero) k) * x k
      = ∑ k, toReal (M i k) * x (Fin.castAdd n₂ k)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

-- and the same on the right block
theorem HPolytope.mulVec_padRight {m : ℕ} (M : Mat 𝕋 m n₂) (x : Vec ℝ (n₁ + n₂)) (i : Fin m) :
    (toRealMat (fun i' => Fin.append (fun _ : Fin n₁ => FloatOps.zero) (M i')) *ᵥ x) i
      = (toRealMat M *ᵥ blockRight n₁ n₂ x) i := by
  show ∑ k : Fin (n₁ + n₂), toReal (Fin.append (fun _ => FloatOps.zero) (M i) k) * x k
      = ∑ k, toReal (M i k) * x (Fin.natAdd n₁ k)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
    Finset.sum_const_zero, zero_add]

-- so membership of the padded polytope is membership of that block, both ways
theorem HPolytope.mem_padLeft_iff {P : HPolytope 𝕋 n₁} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (P.padLeft n₂).construct ↔ blockLeft n₁ n₂ x ∈ P.construct := by
  constructor
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · have hh := hle i
      simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft] at hh
      exact hh
    · have hh := heq i
      simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft] at hh
      exact hh
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]
      exact hle i
    · simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]
      exact heq i

-- the mirror statement for the right block
theorem HPolytope.mem_padRight_iff {P : HPolytope 𝕋 n₂} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (HPolytope.padRight n₁ P).construct ↔ blockRight n₁ n₂ x ∈ P.construct := by
  constructor
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · have hh := hle i
      simp only [HPolytope.padRight, HPolytope.mulVec_padRight] at hh
      exact hh
    · have hh := heq i
      simp only [HPolytope.padRight, HPolytope.mulVec_padRight] at hh
      exact hh
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · simp only [HPolytope.padRight, HPolytope.mulVec_padRight]
      exact hle i
    · simp only [HPolytope.padRight, HPolytope.mulVec_padRight]
      exact heq i

end CORALean.Float
