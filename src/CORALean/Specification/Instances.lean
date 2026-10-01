import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.Global.Float.Instances.Real.Instances

/-!
# What a specification set can be checked against, computed

`Contains` and `IsDisjoint` at float representations, generic over the scalar and so ℝ
among them: a box against anything boxable (`IntervalOuter`), and a halfspace polytope
against a box or a zonotope, both of which answer a direction with no solver.

Box against box, `contains` is exact and `isDisjoint` exact up to one margin; against
anything else, as exact as its interval hull, which for a zonotope's `contains` loses
only rounding. A polytope `contains` by bounding the set along every row —
`holds_safeSet_of_bounds` computed — exact up to rounding; `isDisjoint` looks for one
row the set lies strictly beyond — `holds_unsafeSet_of_separating` at the row's
direction, `verifyConvex`'s `safe` exit at a fixed direction list — and so is exact
only for a halfspace. `ltStrict`'s margin is what makes a separation strict.

The box-against-`IntervalOuter` instance above is generic over a family `S : ℕ → Type`,
which instance search cannot read off a real-layer family written as a lambda
(`Real.Zonotope (Vec ℝ n)` does not unify with `S n`): fixing `S` to each exact real
representation below is what makes those fire.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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
def aux_zonoBound (Z : Zonotope 𝕋 n) (a : Vec 𝕋 n) : 𝕋 :=
  (Z.boundDot (c := aux_dirLin a) a fun _ => rfl).val

theorem aux_zonoBound_le (Z : Zonotope 𝕋 n) :
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
    toReal (neg (bnd fun j => neg (a j))) ≤ ∑ j, toReal (a j) * x j := by
  have h := hb (fun j => neg (a j)) x hx
  simp only [toReal_neg, neg_mul, Finset.sum_neg_distrib] at h
  rw [toReal_neg]
  linarith

/-- Every row of `P` bounded on the set by `bnd`, an equality row from both sides. -/
def aux_containsRows (P : HPolytope 𝕋 n) (bnd : Vec 𝕋 n → 𝕋) : Bool :=
  (List.finRange P.m).all (fun i => le (bnd (P.A i)) (P.b i)) &&
    (List.finRange P.me).all fun i =>
      le (bnd (P.Ae i)) (P.be.sup i) && le (P.be.inf i) (neg (bnd fun j => neg (P.Ae i j)))

theorem aux_containsRows_sound {P : HPolytope 𝕋 n} {X : Set (Vec ℝ n)} {bnd : Vec 𝕋 n → 𝕋}
    (hb : ∀ a, ∀ x ∈ X, ∑ j, toReal (a j) * x j ≤ toReal (bnd a))
    (h : aux_containsRows P bnd = true) : X ⊆ P.construct := by -- --- PROOF ---
  simp only [aux_containsRows, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  intro x hx
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · exact le_trans (hb (P.A i) x hx) (toReal_le_of_le (h.1 i))
  · exact le_trans (toReal_le_of_le (h.2 i).2) (aux_neg_bound hb (P.Ae i) hx)
  · exact le_trans (hb (P.Ae i) x hx) (toReal_le_of_le (h.2 i).1)

/-- One row of `P` the whole set lies strictly beyond. -/
def aux_disjointRows (P : HPolytope 𝕋 n) (bnd : Vec 𝕋 n → 𝕋) : Bool :=
  (List.finRange P.m).any fun i => ltStrict (P.b i) (neg (bnd fun j => neg (P.A i j)))

theorem aux_disjointRows_sound {P : HPolytope 𝕋 n} {X : Set (Vec ℝ n)} {bnd : Vec 𝕋 n → 𝕋}
    (hb : ∀ a, ∀ x ∈ X, ∑ j, toReal (a j) * x j ≤ toReal (bnd a))
    (h : aux_disjointRows P bnd = true) : Disjoint X P.construct := by -- --- PROOF ---
  simp only [aux_disjointRows, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨i, hi⟩ := h
  rw [Set.disjoint_left]
  intro x hX hP
  have hrow : ∑ j, toReal (P.A i j) * x j ≤ toReal (P.b i) :=
    (HPolytope.mem_construct_iff.mp hP).1 i
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

instance containsPolytopeInterval : Contains (HPolytope 𝕋 n) (Interval (Vec 𝕋 n)) where
  contains P I := aux_containsRows P (aux_boxBound I)
  contains_sound _ I := aux_containsRows_sound (aux_boxBound_le I)

instance containsPolytopeZonotope : Contains (HPolytope 𝕋 n) (Zonotope 𝕋 n) where
  contains P Z := aux_containsRows P (aux_zonoBound Z)
  contains_sound _ Z := aux_containsRows_sound (aux_zonoBound_le Z)

instance isDisjointPolytopeInterval : IsDisjoint (HPolytope 𝕋 n) (Interval (Vec 𝕋 n)) where
  isDisjoint P I := aux_disjointRows P (aux_boxBound I)
  isDisjoint_sound _ I := aux_disjointRows_sound (aux_boxBound_le I)

instance isDisjointPolytopeZonotope : IsDisjoint (HPolytope 𝕋 n) (Zonotope 𝕋 n) where
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
