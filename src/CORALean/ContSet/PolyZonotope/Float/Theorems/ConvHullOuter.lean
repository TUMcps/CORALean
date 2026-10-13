module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.ConvHull
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `convHull` contains both operands, over a floating-point scalar

As over ℝ, `Real.PolyZonotope.union_subset_convHull`: a point of either operand is a point of its
dependent part, which the two chord sets of `linComb_outer` put in the result, plus a point of its
independent zonotope, which `Zonotope.linComb_outer` puts in `enclose(Z1, Z2)`. The sum is a point
of the result because the zonotope's generators are its independent block, and its rounded centre
and its error box are in the error box.

Both operands must denote a point: the chord of a set with the empty one is empty, and CORA returns
`pZ` when `S` is empty before it gets here.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero-centred zonotope of the independent block, as `convHull` builds it. -/
abbrev PolyZonotope.aux_Z (P : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  ⟨P.q, fun _ => zero, P.GI, Interval.origin n⟩

/-- The dependent value at `a`, plus an error, is a point of the operand without its independent
block. -/
theorem PolyZonotope.aux_dep_mem (P : PolyZonotope (Vec 𝕋 n)) {a : Fin P.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) {e : Vec ℝ n} (he : e ∈ P.err.construct) :
    (fun i => toReal (P.c i) + ∑ l, toReal (P.G l i) * Real.PolyZonotope.monomial P.E a l) + e
      ∈ P.noIndep.construct :=
  Set.add_mem_add (PolyZonotope.mem_nominalSet_iff.mpr
    ⟨a, Fin.elim0, ha, fun j => j.elim0, fun i => by simp [PolyZonotope.noIndep]; rfl⟩) he


/-- The independent value is a point of the zonotope of the independent block. -/
theorem PolyZonotope.aux_ind_mem (P : PolyZonotope (Vec 𝕋 n)) {β : Fin P.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, toReal (P.GI j i) * β j)
      ∈ (PolyZonotope.aux_Z P).construct := by -- --- PROOF ---
  have h0 : (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct := by
    rw [Interval.origin_exact]
    exact Set.mem_singleton _
  have hz : (fun i => ∑ j, toReal (P.GI j i) * β j) + 0
      ∈ InflatedContSet.nominalSet (PolyZonotope.aux_Z P)
        + (Interval.origin n : Interval (Vec 𝕋 n)).construct :=
    Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => by
      simp [toReal_zero]⟩) h0
  rw [add_zero] at hz
  exact hz


/-- A point of an operand's dependent part is a chord of that part with itself. -/
theorem PolyZonotope.aux_chord (P : PolyZonotope (Vec 𝕋 n)) {y : Vec ℝ n} (hy : y ∈ P.construct) :
    y ∈ (P.linComb P).construct :=
  PolyZonotope.linComb_outer P P ⟨y, hy, y, hy, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- A point of the first dependent part is in the chords of chords. -/
theorem PolyZonotope.aux_left (A B : PolyZonotope (Vec 𝕋 n)) {y₁ y₂ : Vec ℝ n}
    (h₁ : y₁ ∈ A.construct) (h₂ : y₂ ∈ B.construct) :
    y₁ ∈ ((A.linComb A).linComb (B.linComb B)).construct :=
  PolyZonotope.linComb_outer _ _ ⟨y₁, PolyZonotope.aux_chord A h₁, y₂,
    PolyZonotope.aux_chord B h₂, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- A point of the second dependent part is in the chords of chords. -/
theorem PolyZonotope.aux_right (A B : PolyZonotope (Vec 𝕋 n)) {y₁ y₂ : Vec ℝ n}
    (h₁ : y₁ ∈ A.construct) (h₂ : y₂ ∈ B.construct) :
    y₂ ∈ ((A.linComb A).linComb (B.linComb B)).construct :=
  PolyZonotope.linComb_outer _ _ ⟨y₁, PolyZonotope.aux_chord A h₁, y₂,
    PolyZonotope.aux_chord B h₂, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩


/-- A point of the first zonotope is in `enclose(Z1, Z2)`. -/
theorem PolyZonotope.aux_zono_left (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) {z : Vec ℝ n}
    (hz : z ∈ Z₁.construct)
    (h0 : (0 : Vec ℝ n) ∈ Z₂.construct) : z ∈ (Z₁.linComb Z₂).construct :=
  Zonotope.linComb_outer Z₁ Z₂ ⟨z, hz, 0, h0, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- A point of the second zonotope is in `enclose(Z1, Z2)`. -/
theorem PolyZonotope.aux_zono_right (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) {z : Vec ℝ n}
    (hz : z ∈ Z₂.construct)
    (h0 : (0 : Vec ℝ n) ∈ Z₁.construct) : z ∈ (Z₁.linComb Z₂).construct :=
  Zonotope.linComb_outer Z₁ Z₂ ⟨0, h0, z, hz, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩

/-- A point of the chords of chords plus a point of `enclose(Z1, Z2)` is a point of the result. -/
theorem PolyZonotope.aux_assemble (P₁ P₂ : PolyZonotope (Vec 𝕋 n)) {d z : Vec ℝ n}
    (hd : d ∈ ((P₁.noIndep.linComb P₁.noIndep).linComb (P₂.noIndep.linComb P₂.noIndep)).construct)
    (hz : z ∈ ((PolyZonotope.aux_Z P₁).linComb (PolyZonotope.aux_Z P₂)).construct) :
    d + z ∈ (P₁.convHull P₂).construct := by -- --- PROOF ---
  obtain ⟨nR, hnR, eR, heR, rfl⟩ := hd
  obtain ⟨nZ, hnZ, eZ, heZ, rfl⟩ := hz
  obtain ⟨aR, βR, haR, -, hR⟩ := PolyZonotope.mem_nominalSet_iff.mp hnR
  obtain ⟨β, hβ, hZ⟩ := Zonotope.mem_nominalSet_iff.mp hnZ
  -- no independent generator is left in the chords of chords
  haveI : IsEmpty (Fin ((P₁.noIndep.linComb P₁.noIndep).linComb
      (P₂.noIndep.linComb P₂.noIndep)).q) := inferInstanceAs (IsEmpty (Fin 0))
  refine Set.mem_add.mpr ⟨_, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨aR, β, haR, hβ, fun i => rfl⟩, _, Interval.plus_outer _ _
      (Set.add_mem_add heR (Interval.plus_outer _ _ (Set.add_mem_add heZ
        (Interval.mem_point _)))), ?_⟩
  funext i
  have h1 := hR i
  have h2 := hZ i
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h1
  dsimp only [PolyZonotope.convHull]
  have h3 : ∀ v : Vec 𝕋 n, toRealVec v i = toReal (v i) := fun v => rfl
  simp only [Pi.add_apply, h1, h2, RealImage.realImage, h3]
  -- the same six terms, in another order (the sums agree by unfolding `convHull`)
  have key : ∀ x sZ eR eZ cZ : ℝ, x + sZ + (eR + (eZ + cZ)) = x + eR + (cZ + sZ + eZ) :=
    fun x sZ eR eZ cZ => by ring
  exact key _ _ _ _ _


/-- The origin is in the zonotope of the independent block. -/
theorem PolyZonotope.aux_zero_mem (P : PolyZonotope (Vec 𝕋 n)) :
    (0 : Vec ℝ n) ∈ (PolyZonotope.aux_Z P).construct := by
  have h := PolyZonotope.aux_ind_mem P (β := fun _ => 0) (fun _ => by simp)
  simp only [mul_zero, Finset.sum_const_zero] at h
  exact h

/-- A point of an operand is a dependent point with an error, plus an independent one. -/
theorem PolyZonotope.aux_decomp (P : PolyZonotope (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ P.construct) :
    ∃ d z : Vec ℝ n, x = d + z ∧ d ∈ P.noIndep.construct ∧
      z ∈ (PolyZonotope.aux_Z P).construct := by -- --- PROOF ---
  obtain ⟨nx, hn, e, he, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨a, β, ha, hβ, hnx⟩ := PolyZonotope.mem_nominalSet_iff.mp hn
  refine ⟨_, _, ?_, PolyZonotope.aux_dep_mem P ha he, PolyZonotope.aux_ind_mem P hβ⟩
  funext i
  simp only [Pi.add_apply, hnx i]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.convHull_outer (P₁ P₂ : PolyZonotope (Vec 𝕋 n)) (h₁ : P₁.construct.Nonempty)
    (h₂ : P₂.construct.Nonempty) :
    P₁.construct ∪ P₂.construct ⊆ (P₁.convHull P₂).construct := by -- --- PROOF ---
  -- a dependent point of the other operand to pair with
  obtain ⟨d₁, -, -, hd₁, -⟩ := PolyZonotope.aux_decomp P₁ h₁.some_mem
  obtain ⟨d₂, -, -, hd₂, -⟩ := PolyZonotope.aux_decomp P₂ h₂.some_mem
  rintro x (hx | hx)
  · obtain ⟨d, z, rfl, hd, hz⟩ := PolyZonotope.aux_decomp P₁ hx
    exact PolyZonotope.aux_assemble P₁ P₂ (PolyZonotope.aux_left _ _ hd hd₂)
      (PolyZonotope.aux_zono_left _ _ hz (PolyZonotope.aux_zero_mem P₂))
  · obtain ⟨d, z, rfl, hd, hz⟩ := PolyZonotope.aux_decomp P₂ hx
    exact PolyZonotope.aux_assemble P₁ P₂ (PolyZonotope.aux_right _ _ hd₁ hd)
      (PolyZonotope.aux_zono_right _ _ hz (PolyZonotope.aux_zero_mem P₁))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
