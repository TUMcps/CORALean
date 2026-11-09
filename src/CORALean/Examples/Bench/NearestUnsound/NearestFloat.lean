import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# Round-to-nearest binary64, WITHOUT guarantees

The paper's baseline, "round-to-nearest (as in CORA)": a native `Float` whose four rounded
operations are the machine's round-to-nearest ones, both directions alike, so `addUp a b` and
`addDown a b` are the same `a + b`. That is what CORA computes with, and it bounds nothing in any
direction. A one-field structure rather than `Float` itself, so that no instance written for
`Float` applies to it by accident; the compiler erases the wrapper. The laws that stay true (`neg`,
`min`, `max`, `≤`, `half`, the constants) are proved in `Instances` from
`Binary64.trustedHardware`; the six false ones are fields of `IsNearestUnsound`, assumed by the
false axiom in `Axioms` (see `scripts/check-axioms.sh`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   07-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A binary64 computed with round-to-nearest in both directions. Unsound: a
bench baseline only. -/
structure NearestFloat where
  val : Float

namespace NearestFloat

/-- The number the bits denote, exactly as for `Float`. -/
def toReal (a : NearestFloat) : ℝ := Binary64.toReal a.val

/-- The machine's round-to-nearest sum, used as `addUp` and `addDown` both. -/
def add (a b : NearestFloat) : NearestFloat := ⟨a.val + b.val⟩

/-- The machine's round-to-nearest product, used as `mulUp` and `mulDown` both. -/
def mul (a b : NearestFloat) : NearestFloat := ⟨a.val * b.val⟩

/-- The machine's round-to-nearest quotient, used as `divUp` and `divDown` both. -/
def div (a b : NearestFloat) : NearestFloat := ⟨a.val / b.val⟩

/-- The machine's correctly rounded square root, used as `sqrtUp`; the number of Newton
steps is ignored. -/
def sqrt (_p : ℕ) (a : NearestFloat) : NearestFloat := ⟨Float.sqrt a.val⟩

/-- The machine's (libm's) elementary functions, used as the lower and the upper bound alike:
`sinDown`, `sinUp`, `expUp`, `logDown`, `atanUp` and the others; the number of halvings, of
bisection steps and of Newton steps is ignored. -/
def elem : ElemOverride NearestFloat where
  sin a := ⟨Float.sin a.val⟩
  cos a := ⟨Float.cos a.val⟩
  exp a := ⟨Float.exp a.val⟩
  log a := ⟨Float.log a.val⟩
  tan a := ⟨Float.tan a.val⟩
  atan a := ⟨Float.atan a.val⟩

end NearestFloat

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
