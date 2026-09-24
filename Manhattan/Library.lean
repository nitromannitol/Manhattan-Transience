/-
The abstract operator objects of Section 2 of the paper are those of the
library modules `LatticeProb.Analysis.DissipativeSkewOperator` and
`LatticeProb.Analysis.OperatorSemigroup`: the dissipative-skew pair
`G = S + A` with its coercive resolvents, and the semigroup of a bounded
generator with its Laplace resolvent.  The frozen statements under
`Manhattan/Frozen/Operator/` name them with the `Manhattan.Operator` prefix, so
they are re-exported here under that namespace.
-/
import LatticeProb.Analysis.DissipativeSkewOperator
import LatticeProb.Analysis.OperatorSemigroup

namespace Manhattan.Operator

export LatticeProb.Analysis (DissipativeSkewPair operatorSemigroup resolventOperator dampedOrbit
  laplaceVector resolventEquiv semigroupCorrelation)

end Manhattan.Operator

namespace Manhattan.Operator.DissipativeSkewPair

export LatticeProb.Analysis.DissipativeSkewPair (realForm)

end Manhattan.Operator.DissipativeSkewPair
