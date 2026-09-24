import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.ContSet.Operations.SupportBoundSegments
import CORALean.ContSet.HPolytope.Real.Operations.Rows
import CORALean.ContSet.HPolytope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBoundsOpt
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact
import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMem

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

`Plus` and `LinComb` at `Vec ℝ n`, where `supportBound` answers a direction by
simplex. A description with no rows is still unbounded and still has no bound,
so the answer is an `Option` and an unanswered direction contributes the vacuous
row `0 x ≤ 0`: total without a type that excludes unbounded sets. The directions
are the operands' own rows, among which a sum's facet normals lie.

Not `Mtimes`: no direction on the target is named by the operands, so the choice
would be a precision one and instance search may not make one. `Intersection` and
`OfPoint` land too — the latter only at `Vec ℝ n`, `LinearMap.proj` needing
coordinates — `mapEquiv` backs `Reindex` below, and `comap`, `translate` stay
named. `OfInterval` would land as it stands, but its class lives in `Conversion`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (HPolytope α) α := ⟨HPolytope.construct⟩

instance : Reduce (HPolytope α) α where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : Intersection (HPolytope α) α where
  intersection := HPolytope.intersection
  intersection_outer P₁ P₂ := (HPolytope.intersection_exact P₁ P₂).subset

/-- At `Vec ℝ n` alone: `LinearMap.proj`, which reads a point's equality rows
back, needs coordinates. -/
instance {n : ℕ} : OfPoint (HPolytope (Vec ℝ n)) (Vec ℝ n) where
  ofPoint := HPolytope.ofPoint
  mem_ofPoint := HPolytope.mem_ofPoint

/-- A sum enclosed on the operands' own rows, each bound certified against the
dual candidate a simplex proposed. A direction with no bound contributes no
constraint, which is what makes this total. -/
noncomputable instance {n : ℕ} : Plus (HPolytope (Vec ℝ n)) (Vec ℝ n) where
  plus P₁ P₂ := HPolytope.ofBoundsOpt (Fin.append P₁.rows P₂.rows) fun i =>
    (P₁.supportBound (Fin.append P₁.rows P₂.rows i)).bind fun u =>
      (P₂.supportBound (Fin.append P₁.rows P₂.rows i)).map u.add
  plus_outer _ _ := HPolytope.subset_ofBoundsOpt _ _

/-- The same directions and the same certificates, the larger of the two bounds
serving: a point on a segment between the two beats neither. -/
noncomputable instance {n : ℕ} : LinComb (HPolytope (Vec ℝ n)) (Vec ℝ n) where
  linComb P₁ P₂ := HPolytope.ofBoundsOpt (Fin.append P₁.rows P₂.rows) fun i =>
    (P₁.supportBound (Fin.append P₁.rows P₂.rows i)).bind fun u =>
      (P₂.supportBound (Fin.append P₁.rows P₂.rows i)).map u.segments
  linComb_outer _ _ := HPolytope.subset_ofBoundsOpt _ _

/-- `mapEquiv` wants an equivalence, not a linear map, so a reindexing goes
through `LinearEquiv.funCongrLeft`, whose coercion is `reindexLin` again. -/
instance : Reindex (fun n => HPolytope (Vec ℝ n)) where
  reindex e P := HPolytope.mapEquiv (LinearEquiv.funCongrLeft ℝ ℝ e) P
  reindex_exact e P := (HPolytope.mapEquiv_exact (LinearEquiv.funCongrLeft ℝ ℝ e) P).symm

/-- The halfspace family over vectors, named as `𝒵` names the zonotope one: a
generic `S : ℕ → Type` cannot be read off one member, so a use site writes
`(S := ℋ𝒫)` — or, at a guard, `(G := ℋ𝒫)`. -/
scoped notation "ℋ𝒫" => fun n => HPolytope (Vec ℝ n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
