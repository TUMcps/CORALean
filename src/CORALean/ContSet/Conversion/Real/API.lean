import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope

/-!
# Conversions between representations, collected

One file per ordered pair, named for it. Conversions live here rather than in
either representation because two representations of equal standing cannot each
import the other — `VPolytope` converting to `HPolytope` inside `VPolytope/`
and back inside `HPolytope/` is a cycle Lean rejects. A pair that needs no such
file simply has none, and nothing has to be reorganised when one is added.

The exception is a conversion a representation needs for its *own* operations,
which has to sit below it: `VPolytope.ofInterval` and `VPolytope.interval` stay
in `VPolytope/`, since `VPolytope.and` is built from them.
-/
