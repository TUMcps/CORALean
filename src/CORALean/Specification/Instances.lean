module

public import CORALean.ContSet.Capsule.Float.Instances
public import CORALean.ContSet.Capsule.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.ContSet.Definitions.FullDimTest
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Polygon.Float.Theorems.IsDisjointSound
public import CORALean.ContSet.Polygon.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.VPolytope.Float.Instances
public import CORALean.ContSet.VPolytope.Float.Operations.IsFullDim
public import CORALean.ContSet.VPolytope.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ZonoBundle.Float.Instances
public import CORALean.ContSet.ConPolyZono.Float.Instances
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.ConZonotope.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.HPolytope.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.PolyZonotope.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound
public import CORALean.ContSet.Zonotope.Float.Theorems.IsFullDimSound
public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# What a specification set can be checked against, computed

`Contains` and `IsDisjoint` at float representations, generic over the scalar and so ℝ
among them: a box against anything boxable (`IntervalOuter`), and a halfspace polytope
against a box or a zonotope, both of which answer a direction with no solver.

Box against box, `contains` is exact and `isDisjoint` exact up to one margin. A polytope `contains`
by bounding the set along every row, exact up to rounding; `isDisjoint` looks for one row the set
lies strictly beyond, so is exact only for a halfspace. Two boxable sets, or a zonotope bundle (one
member's hull), are separated by their hulls: CORA's `'approx'` `isIntersecting_`.

The box-against-`IntervalOuter` instance above is generic over a family `S : ℕ → Type`,
which instance search cannot read off a real-layer family written as a lambda
(`Real.Zonotope (Vec ℝ n)` does not unify with `S n`): fixing `S` to each exact real
representation below is what makes those fire.

`FullDimTest` at the float representations with a sound full-dimension test: a `true` is an
interior point of the set, certified by `ltStrict`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `a` read as the functional over ℝ it names, one row of a one-row matrix. -/
abbrev aux_dirLin (a : Vec 𝕋 n) : Vec ℝ n →ₗ[ℝ] ℝ := rowLin (fun (_ : Fin 1) => a) 0

/-- A box's bound along `a`. -/
def aux_boxBound (I : Interval (Vec 𝕋 n)) (a : Vec 𝕋 n) : 𝕋 :=
  (I.boundDot (c := aux_dirLin a) a fun _ => rfl).val

theorem aux_boxBound_le (I : Interval (Vec 𝕋 n)) :
    ∀ a, ∀ x ∈ I.construct, ∑ j, toReal (a j) * x j ≤ toReal (aux_boxBound I a) :=
  fun a => (I.boundDot (c := aux_dirLin a) a fun _ => rfl).le

/-- A zonotope's bound along `a`, with no solver. -/
def aux_zonoBound (Z : Zonotope (Vec 𝕋 n)) (a : Vec 𝕋 n) : 𝕋 :=
  (Z.boundDot (c := aux_dirLin a) a fun _ => rfl).val

theorem aux_zonoBound_le (Z : Zonotope (Vec 𝕋 n)) :
    ∀ a, ∀ x ∈ Z.construct, ∑ j, toReal (a j) * x j ≤ toReal (aux_zonoBound Z a) :=
  fun a => (Z.boundDot (c := aux_dirLin a) a fun _ => rfl).le

/-- Every coordinate of `B` inside `I`'s. -/
def aux_containsBox (I B : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => le (I.inf j) (B.inf j) && le (B.sup j) (I.sup j)

theorem aux_containsBox_sound {I B : Interval (Vec 𝕋 n)} (h : aux_containsBox I B = true) :
    B.construct ⊆ I.construct := by -- --- PROOF ---
  simp only [aux_containsBox, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    forall_const] at h
  intro x hx j
  have hlo : toReal (B.inf j) ≤ x j := (hx j).1
  have hhi : x j ≤ toReal (B.sup j) := (hx j).2
  exact ⟨le_trans (toReal_le_of_le (h j).1) hlo, le_trans hhi (toReal_le_of_le (h j).2)⟩

/-- One coordinate in which `B` lies strictly to one side of `I`. -/
def aux_disjointBox (I B : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).any fun j => ltStrict (B.sup j) (I.inf j) || ltStrict (I.sup j) (B.inf j)

theorem aux_disjointBox_sound {I B : Interval (Vec 𝕋 n)} (h : aux_disjointBox I B = true) :
    Disjoint B.construct I.construct := by -- --- PROOF ---
  simp only [aux_disjointBox, List.any_eq_true, List.mem_finRange, Bool.or_eq_true,
    true_and] at h
  obtain ⟨j, hj⟩ := h
  rw [Set.disjoint_left]
  intro x hB hI
  have hB₁ : toReal (B.inf j) ≤ x j := (hB j).1
  have hB₂ : x j ≤ toReal (B.sup j) := (hB j).2
  have hI₁ : toReal (I.inf j) ≤ x j := (hI j).1
  have hI₂ : x j ≤ toReal (I.sup j) := (hI j).2
  rcases hj with hj | hj
  · linarith [toReal_lt_of_ltStrict hj]
  · linarith [toReal_lt_of_ltStrict hj]

/-- The negated direction's bound, read as a lower bound along `a`. -/
theorem aux_neg_bound {X : Set (Vec ℝ n)} {bnd : Vec 𝕋 n → 𝕋}
    (hb : ∀ a, ∀ x ∈ X, ∑ j, toReal (a j) * x j ≤ toReal (bnd a)) (a : Vec 𝕋 n)
    {x : Vec ℝ n} (hx : x ∈ X) :
    toReal (neg (bnd (-a))) ≤ ∑ j, toReal (a j) * x j := by
  have h := hb (-a) x hx
  simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib] at h
  rw [toReal_neg]
  linarith

/-- Every row of `P` bounded on the set by `bnd`, an equality row from both sides, and the origin
in the error box, so that the nominal part the rows describe is inside the polytope. -/
def aux_containsRows (P : HPolytope 𝕋 (Vec 𝕋 n)) (bnd : Vec 𝕋 n → 𝕋) : Bool :=
  (List.finRange P.m).all (fun i => le (bnd (P.A i)) (P.b i)) &&
    (List.finRange P.me).all (fun i =>
      le (bnd (P.Ae i)) (P.be i) && le (P.be i) (neg (bnd (-(P.Ae i))))) &&
    (List.finRange n).all fun j => le (P.I_error.inf j) zero && le zero (P.I_error.sup j)

theorem aux_containsRows_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {X : Set (Vec ℝ n)} {bnd : Vec 𝕋 n → 𝕋}
    (hb : ∀ a, ∀ x ∈ X, ∑ j, toReal (a j) * x j ≤ toReal (bnd a))
    (h : aux_containsRows P bnd = true) : X ⊆ P.construct := by -- --- PROOF ---
  simp only [aux_containsRows, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  intro x hx
  obtain ⟨⟨hA, hE⟩, hbox⟩ := h
  refine ⟨x, HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩, 0, ?_, add_zero x⟩
  · exact le_trans (hb (P.A i) x hx) (toReal_le_of_le (hA i))
  · exact le_antisymm (le_trans (hb (P.Ae i) x hx) (toReal_le_of_le (hE i).1))
      (le_trans (toReal_le_of_le (hE i).2) (aux_neg_bound hb (P.Ae i) hx))
  · refine Interval.mem_vec_iff.mpr fun j => ?_
    have h₁ := toReal_le_of_le (hbox j).1
    have h₂ := toReal_le_of_le (hbox j).2
    rw [toReal_zero] at h₁ h₂
    exact ⟨h₁, h₂⟩

/-- One row of `P` the whole set lies strictly beyond. -/
def aux_disjointRows (P : HPolytope 𝕋 (Vec 𝕋 n)) (bnd : Vec 𝕋 n → 𝕋) : Bool :=
  (List.finRange P.m).any fun i => ltStrict (P.bU i) (neg (bnd (-(P.A i))))

theorem aux_disjointRows_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {X : Set (Vec ℝ n)} {bnd : Vec 𝕋 n → 𝕋}
    (hb : ∀ a, ∀ x ∈ X, ∑ j, toReal (a j) * x j ≤ toReal (bnd a))
    (h : aux_disjointRows P bnd = true) : Disjoint X P.construct := by -- --- PROOF ---
  simp only [aux_disjointRows, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨i, hi⟩ := h
  rw [Set.disjoint_left]
  intro x hX hP
  have hrow : ∑ j, toReal (P.A i j) * x j ≤ toReal (P.bU i) :=
    (HPolytope.rows_of_mem_construct hP).1 i
  linarith [aux_neg_bound hb (P.A i) hX, toReal_lt_of_ltStrict hi]


-- ========================================  INSTANCES  ========================================= --

/-- Through the interval hull, so exact at a box and, for `contains`, at a zonotope. -/
instance containsBoxOuter {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S 𝕋] :
    Contains (Interval (Vec 𝕋 n)) (S n) where
  contains I s := aux_containsBox I (IntervalOuter.interval s)
  contains_sound _ s h := (IntervalOuter.interval_outer s).trans (aux_containsBox_sound h)

/-- Axis-aligned separation of the interval hull: conservative beyond a box. -/
instance isDisjointBoxOuter {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S 𝕋] :
    IsDisjoint (Interval (Vec 𝕋 n)) (S n) where
  isDisjoint I s := aux_disjointBox I (IntervalOuter.interval s)
  isDisjoint_sound _ s h := (aux_disjointBox_sound h).mono_left (IntervalOuter.interval_outer s)

/-- Each set through its interval hull, `'approx'` `isIntersecting_`: `true` separates the hulls,
`false` says nothing. Low priority, so the box and polytope instances above come first. -/
instance (priority := 50) isDisjointBoxBoxOuter {T S : ℕ → Type}
    [∀ n, ContSet (T n) (Vec ℝ n)] [∀ n, ContSet (S n) (Vec ℝ n)]
    [IntervalOuter T 𝕋] [IntervalOuter S 𝕋] : IsDisjoint (T n) (S n) where
  isDisjoint t s := aux_disjointBox (IntervalOuter.interval t) (IntervalOuter.interval s)
  isDisjoint_sound t s h :=
    (aux_disjointBox_sound h).mono (IntervalOuter.interval_outer s)
      (IntervalOuter.interval_outer t)

/-- Some member's hull of `zB` strictly to one side of `B`. -/
def aux_disjointBundleBox (zB : ZonoBundle (Vec 𝕋 n)) (B : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange zB.k).any fun i => aux_disjointBox (Zonotope.interval (zB.Z i)) B

theorem aux_disjointBundleBox_sound {zB : ZonoBundle (Vec 𝕋 n)} {B : Interval (Vec 𝕋 n)}
    (h : aux_disjointBundleBox zB B = true) :
    Disjoint B.construct zB.construct := by
  simp only [aux_disjointBundleBox, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨i, hi⟩ := h
  exact (aux_disjointBox_sound hi).mono_right
    ((Set.iInter_subset _ i).trans (Zonotope.interval_contains (zB.Z i)))

/-- Some member of `zB'` and some member of `zB` with disjoint hulls. -/
def aux_disjointBundles (zB zB' : ZonoBundle (Vec 𝕋 n)) : Bool :=
  (List.finRange zB'.k).any fun j => aux_disjointBundleBox zB (Zonotope.interval (zB'.Z j))

theorem aux_disjointBundles_sound {zB zB' : ZonoBundle (Vec 𝕋 n)}
    (h : aux_disjointBundles zB zB' = true) :
    Disjoint zB'.construct zB.construct := by
  simp only [aux_disjointBundles, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨j, hj⟩ := h
  exact (aux_disjointBundleBox_sound hj).mono_left
    ((Set.iInter_subset _ j).trans (Zonotope.interval_contains (zB'.Z j)))

-- A bundle's three pairings: with a boxable set on either side, and with a bundle.

/-- A bundle lies in each member, so one member's hull apart from the other hull suffices; the
bundle has no total box of its own (`k = 0` is the whole space). -/
instance (priority := 50) isDisjointZonoBundleOuter {S : ℕ → Type}
    [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S 𝕋] : IsDisjoint
    (ZonoBundle (Vec 𝕋 n)) (S n) where
  isDisjoint zB s := aux_disjointBundleBox zB (IntervalOuter.interval s)
  isDisjoint_sound _ s h :=
    (aux_disjointBundleBox_sound h).mono_left (IntervalOuter.interval_outer s)

-- the same with the bundle second
instance (priority := 50) isDisjointOuterZonoBundle {T : ℕ → Type}
    [∀ n, ContSet (T n) (Vec ℝ n)] [IntervalOuter T 𝕋] : IsDisjoint (T n)
    (ZonoBundle (Vec 𝕋 n)) where
  isDisjoint t zB := aux_disjointBundleBox zB (IntervalOuter.interval t)
  isDisjoint_sound t _ h :=
    (aux_disjointBundleBox_sound h).symm.mono_right (IntervalOuter.interval_outer t)

-- and a bundle against a bundle
instance (priority := 50) isDisjointZonoBundleZonoBundle :
    IsDisjoint (ZonoBundle (Vec 𝕋 n)) (ZonoBundle (Vec 𝕋 n)) where
  isDisjoint := aux_disjointBundles
  isDisjoint_sound _ _ := aux_disjointBundles_sound

/-- The box's pair at a float zonotope, `S` fixed rather than inferred: the generic instances
above cannot find a family written as a lambda. -/
instance containsBoxZonotope : Contains (Interval (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) :=
  containsBoxOuter (S := 𝒵[𝕋])

instance isDisjointBoxZonotope : IsDisjoint (Interval (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) :=
  isDisjointBoxOuter (S := 𝒵[𝕋])

instance containsPolytopeInterval : Contains (HPolytope 𝕋 (Vec 𝕋 n)) (Interval (Vec 𝕋 n)) where
  contains P I := aux_containsRows P (aux_boxBound I)
  contains_sound _ I := aux_containsRows_sound (aux_boxBound_le I)

instance containsPolytopeZonotope : Contains (HPolytope 𝕋 (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) where
  contains P Z := aux_containsRows P (aux_zonoBound Z)
  contains_sound _ Z := aux_containsRows_sound (aux_zonoBound_le Z)

instance isDisjointPolytopeInterval : IsDisjoint (HPolytope 𝕋 (Vec 𝕋 n)) (Interval (Vec 𝕋 n)) where
  isDisjoint P I := aux_disjointRows P (aux_boxBound I)
  isDisjoint_sound _ I := aux_disjointRows_sound (aux_boxBound_le I)

instance isDisjointPolytopeZonotope : IsDisjoint (HPolytope 𝕋 (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) where
  isDisjoint P Z := aux_disjointRows P (aux_zonoBound Z)
  isDisjoint_sound _ Z := aux_disjointRows_sound (aux_zonoBound_le Z)

open scoped CORALean.Real in
/-- The box's `Contains`/`IsDisjoint` at an exact real-layer family, `S` fixed rather than
inferred — what the generic instance above cannot do at a family written as a lambda. -/
noncomputable instance containsBoxRealInterval :
    Contains (Interval (Vec ℝ n)) (Real.Interval (Vec ℝ n)) where
  contains I s := aux_containsBox I (IntervalOuter.interval (S := ℐ𝒱) s)
  contains_sound _ s h :=
    (IntervalOuter.interval_outer (S := ℐ𝒱) s).trans (aux_containsBox_sound h)

open scoped CORALean.Real in
noncomputable instance isDisjointBoxRealInterval :
    IsDisjoint (Interval (Vec ℝ n)) (Real.Interval (Vec ℝ n)) where
  isDisjoint I s := aux_disjointBox I (IntervalOuter.interval (S := ℐ𝒱) s)
  isDisjoint_sound _ s h :=
    (aux_disjointBox_sound h).mono_left (IntervalOuter.interval_outer (S := ℐ𝒱) s)

-- The same pair at the second exact family a box can be hulled from.
open scoped CORALean.Real in
noncomputable instance containsBoxRealZonotope :
    Contains (Interval (Vec ℝ n)) (Real.Zonotope (Vec ℝ n)) where
  contains I s := aux_containsBox I (IntervalOuter.interval (S := 𝒵) s)
  contains_sound _ s h :=
    (IntervalOuter.interval_outer (S := 𝒵) s).trans (aux_containsBox_sound h)

open scoped CORALean.Real in
noncomputable instance isDisjointBoxRealZonotope :
    IsDisjoint (Interval (Vec ℝ n)) (Real.Zonotope (Vec ℝ n)) where
  isDisjoint I s := aux_disjointBox I (IntervalOuter.interval (S := 𝒵) s)
  isDisjoint_sound _ s h :=
    (aux_disjointBox_sound h).mono_left (IntervalOuter.interval_outer (S := 𝒵) s)

-- The same pair once more, at the third exact family a box can be hulled from.
open scoped CORALean.Real in
noncomputable instance containsBoxRealConZonotope :
    Contains (Interval (Vec ℝ n)) (Real.ConZonotope (Vec ℝ n)) where
  contains I s := aux_containsBox I (IntervalOuter.interval (S := 𝒞) s)
  contains_sound _ s h :=
    (IntervalOuter.interval_outer (S := 𝒞) s).trans (aux_containsBox_sound h)

open scoped CORALean.Real in
noncomputable instance isDisjointBoxRealConZonotope :
    IsDisjoint (Interval (Vec ℝ n)) (Real.ConZonotope (Vec ℝ n)) where
  isDisjoint I s := aux_disjointBox I (IntervalOuter.interval (S := 𝒞) s)
  isDisjoint_sound _ s h :=
    (aux_disjointBox_sound h).mono_left (IntervalOuter.interval_outer (S := 𝒞) s)

/-- Every width certified positive by `ltStrict`. -/
instance fullDimTestInterval : FullDimTest (Interval (Vec 𝕋 n)) where
  isFullDim := Interval.isFullDim
  isFullDim_sound _ h := Interval.isFullDim_sound h

/-- The exact characterisation, each comparison certified. -/
instance fullDimTestCapsule : FullDimTest (Capsule 𝕋 n) where
  isFullDim := Capsule.isFullDim
  isFullDim_sound _ h := Capsule.isFullDim_sound h

/-- A piece with a nonempty box and three vertices whose cross product is certified nonzero. -/
instance fullDimTestPolygon : FullDimTest (Polygon 𝕋) where
  isFullDim := Polygon.isFullDim
  isFullDim_sound _ h := Polygon.isFullDim_sound h

/-- Sadraddini and Tedrake's `'approx:st'`, made rounding-proof: approximate coefficients from the
default right inverse of the container's generators, the leftover absorbed by a certified box.
Strict: a set touching the container's boundary is not accepted. -/
instance containsZonotopeZonotope : Contains (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) where
  contains Z₂ Z₁ := Z₂.containsZonotope Z₁ (Zonotope.rightInvCandidate fun i j => Z₂.G j i)
  contains_sound _ _ h := Zonotope.containsZonotope_sound h

/-- A checked right inverse of the generator matrix: a box of positive radius around the center
is reached with coefficients in `[-1, 1]`. -/
instance fullDimTestZonotope : FullDimTest (Zonotope (Vec 𝕋 n)) where
  isFullDim := Zonotope.isFullDim
  isFullDim_sound _ h := Zonotope.isFullDim_sound h

/-- The origin proposed as the interior point: `true` where every row is strictly slack there. A
caller with a better point (a Chebyshev center) calls `HPolytope.isFullDim` itself. -/
instance fullDimTestHPolytope : FullDimTest (HPolytope 𝕋 (Vec 𝕋 n)) where
  isFullDim P := P.isFullDim fun _ => zero
  isFullDim_sound _ h := HPolytope.isFullDim_sound h

/-- The default right inverse of the vertex matrix bordered with a row of ones: `true` for
vertices that affinely span the space, certified. -/
instance fullDimTestVPolytope : FullDimTest (VPolytope (Vec 𝕋 n)) where
  isFullDim := VPolytope.isFullDim
  isFullDim_sound _ h := VPolytope.isFullDim_sound h

/-- The default right inverse, and the origin as the coefficient point: `true` where it lies
strictly inside the constraints. A caller with a better point calls `ConZonotope.isFullDim`. -/
instance fullDimTestConZonotope : FullDimTest (ConZonotope 𝕋 (Vec 𝕋 n)) where
  isFullDim cZ := cZ.isFullDim (Zonotope.rightInvCandidate fun i j => cZ.G j i) fun _ => zero
  isFullDim_sound _ h := ConZonotope.isFullDim_sound h

/-- The default right inverse of the independent generators. -/
instance fullDimTestPolyZonotope : FullDimTest (PolyZonotope (Vec 𝕋 n)) where
  isFullDim := PolyZonotope.isFullDim
  isFullDim_sound _ h := PolyZonotope.isFullDim_sound h

/-- The default right inverse of the independent generators, the factors `0` satisfying the
constraints. -/
instance fullDimTestConPolyZono : FullDimTest (ConPolyZono 𝕋 (Vec 𝕋 n)) where
  isFullDim := ConPolyZono.isFullDim
  isFullDim_sound _ h := ConPolyZono.isFullDim_sound h

/-- The default right inverse of every member, and the first member's center as the common point:
`true` where it is strictly inside every member. A bundle without members is the whole space. -/
instance fullDimTestZonoBundle : FullDimTest (ZonoBundle (Vec 𝕋 n)) where
  isFullDim zB := zB.isFullDim (fun i => Zonotope.rightInvCandidate fun r j => (zB.Z i).G j r)
    (if hk : 0 < zB.k then (zB.Z ⟨0, hk⟩).c else fun _ => zero)
  isFullDim_sound _ h := ZonoBundle.isFullDim_sound h

/-- Every pair of pieces separated along an edge normal, the gap certified by `ltStrict`. -/
instance isDisjointPolygon : IsDisjoint (Polygon 𝕋) (Polygon 𝕋) where
  isDisjoint P Q := Polygon.isDisjoint P Q
  isDisjoint_sound _ _ h := (Polygon.isDisjoint_sound h).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
