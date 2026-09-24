import GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Data

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body6_raw_bound : fineBound 48 body6_raw = true := by
  decide +kernel

theorem body6_result_bound : fineBound 48 body6 = true := by
  decide +kernel

theorem body6_degree0 : equalityCheck (finePart 0 body6_raw) (finePart 0 body6) = true := by
  decide +kernel

theorem body6_degree1 : equalityCheck (finePart 1 body6_raw) (finePart 1 body6) = true := by
  decide +kernel

theorem body6_degree2 : equalityCheck (finePart 2 body6_raw) (finePart 2 body6) = true := by
  decide +kernel

theorem body6_degree3 : equalityCheck (finePart 3 body6_raw) (finePart 3 body6) = true := by
  decide +kernel

theorem body6_degree4 : equalityCheck (finePart 4 body6_raw) (finePart 4 body6) = true := by
  decide +kernel

theorem body6_degree5 : equalityCheck (finePart 5 body6_raw) (finePart 5 body6) = true := by
  decide +kernel

theorem body6_degree6 : equalityCheck (finePart 6 body6_raw) (finePart 6 body6) = true := by
  decide +kernel

theorem body6_degree7 : equalityCheck (finePart 7 body6_raw) (finePart 7 body6) = true := by
  decide +kernel

theorem body6_degree8 : equalityCheck (finePart 8 body6_raw) (finePart 8 body6) = true := by
  decide +kernel

theorem body6_degree9 : equalityCheck (finePart 9 body6_raw) (finePart 9 body6) = true := by
  decide +kernel

theorem body6_degree10 : equalityCheck (finePart 10 body6_raw) (finePart 10 body6) = true := by
  decide +kernel

theorem body6_degree11 : equalityCheck (finePart 11 body6_raw) (finePart 11 body6) = true := by
  decide +kernel

theorem body6_degree12 : equalityCheck (finePart 12 body6_raw) (finePart 12 body6) = true := by
  decide +kernel

theorem body6_degree13 : equalityCheck (finePart 13 body6_raw) (finePart 13 body6) = true := by
  decide +kernel

theorem body6_degree14 : equalityCheck (finePart 14 body6_raw) (finePart 14 body6) = true := by
  decide +kernel

theorem body6_degree15 : equalityCheck (finePart 15 body6_raw) (finePart 15 body6) = true := by
  decide +kernel

theorem body6_degree16 : equalityCheck (finePart 16 body6_raw) (finePart 16 body6) = true := by
  decide +kernel

theorem body6_degree17 : equalityCheck (finePart 17 body6_raw) (finePart 17 body6) = true := by
  decide +kernel

theorem body6_degree18 : equalityCheck (finePart 18 body6_raw) (finePart 18 body6) = true := by
  decide +kernel

theorem body6_degree19 : equalityCheck (finePart 19 body6_raw) (finePart 19 body6) = true := by
  decide +kernel

theorem body6_degree20 : equalityCheck (finePart 20 body6_raw) (finePart 20 body6) = true := by
  decide +kernel

theorem body6_degree21 : equalityCheck (finePart 21 body6_raw) (finePart 21 body6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees
