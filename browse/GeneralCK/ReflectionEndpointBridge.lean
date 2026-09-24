import GeneralCK.Certificates.RegularReflectionExpressionJet
import GeneralCK.ReflectionNormalized

/-!
# Endpoint-safe reflection bridge

The compact reflection expression uses the ratio `e / (a * (1 - z) / 2)`
and therefore cannot be evaluated on a closed certificate box with upper
endpoint `z = 1`.  `RegularReflectionExpression.normalizedValue` uses the
analytic signed contact instead and is defined on that closed box.

The reflection reduction itself only asks for `z < 1`.  Thus a certificate
for the regular expression on a box closed at `1`, together with the strict
physical-side hypothesis, proves the required raw curvature statement.
-/

namespace GeneralCK.Reflection

theorem curvature_pos_of_regular_normalizedValue_pos {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1)
    (hpos : 0 < Certificates.RegularReflectionExpression.normalizedValue a z) :
    0 < curvature a (a * z) := by
  apply curvature_pos_of_normalizedValue_pos ha ha' hz hz'
  rw [← Certificates.RegularReflectionExpression.normalizedValue_eq ha ha' hz hz']
  exact hpos

#print axioms curvature_pos_of_regular_normalizedValue_pos

end GeneralCK.Reflection
