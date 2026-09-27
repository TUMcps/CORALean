import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

/-!
# What trusting native binary64 means, collected

`TrustedHardware` is one property with ten conjuncts, everything `SoundFloatArithmetic` asks of a
scalar; `Axioms` assumes it once, the only `axiom` in the library. Bundled rather than left as
ten separate assumptions so the trust is a single object: one name in every `#print axioms` that
reaches `Float`, one place that says what is being trusted and on which runs, and one thing to
discharge should a verified model of binary64 ever arrive.
-/
