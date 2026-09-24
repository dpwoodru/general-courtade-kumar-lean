import GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Data

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group6_degree44 : equalityCheck (finePart 44 group6_raw) (finePart 44 group6) = true := by
  decide +kernel

theorem group6_degree45 : equalityCheck (finePart 45 group6_raw) (finePart 45 group6) = true := by
  decide +kernel

theorem group6_degree46 : equalityCheck (finePart 46 group6_raw) (finePart 46 group6) = true := by
  decide +kernel

theorem group6_degree47 : equalityCheck (finePart 47 group6_raw) (finePart 47 group6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees
