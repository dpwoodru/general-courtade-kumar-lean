import GeneralCK.Certificates.ReflectionSmallBiasContactDegree16Checks1
import GeneralCK.Certificates.ReflectionSmallBiasContactDegree16Checks2

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body16_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body16_raw) (finePart d body16) = true := by
  interval_cases d
  · exact body16_degree0
  · exact body16_degree1
  · exact body16_degree2
  · exact body16_degree3
  · exact body16_degree4
  · exact body16_degree5
  · exact body16_degree6
  · exact body16_degree7
  · exact body16_degree8
  · exact body16_degree9
  · exact body16_degree10
  · exact body16_degree11
  · exact body16_degree12
  · exact body16_degree13
  · exact body16_degree14
  · exact body16_degree15
  · exact body16_degree16
  · exact body16_degree17
  · exact body16_degree18
  · exact body16_degree19
  · exact body16_degree20
  · exact body16_degree21
  · exact body16_degree22
  · exact body16_degree23
  · exact body16_degree24
  · exact body16_degree25
  · exact body16_degree26
  · exact body16_degree27
  · exact body16_degree28
  · exact body16_degree29
  · exact body16_degree30
  · exact body16_degree31
  · exact body16_degree32
  · exact body16_degree33
  · exact body16_degree34
  · exact body16_degree35
  · exact body16_degree36
  · exact body16_degree37
  · exact body16_degree38
  · exact body16_degree39
  · exact body16_degree40
  · exact body16_degree41
  · exact body16_degree42
  · exact body16_degree43
  · exact body16_degree44
  · exact body16_degree45
  · exact body16_degree46
  · exact body16_degree47

theorem body16_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower16 inversePower15) z = eval k body16 z := by
  have he := eval_eq_of_fineParts 48 k body16_raw body16 z
    (fineBound_sound body16_raw_bound) (fineBound_sound body16_result_bound)
    body16_degrees
  change eval k (normalize body16_raw) z = eval k body16 z
  rw [eval_normalize]
  exact he

theorem group16_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group16_raw) (finePart d group16) = true := by
  interval_cases d
  · exact group16_degree0
  · exact group16_degree1
  · exact group16_degree2
  · exact group16_degree3
  · exact group16_degree4
  · exact group16_degree5
  · exact group16_degree6
  · exact group16_degree7
  · exact group16_degree8
  · exact group16_degree9
  · exact group16_degree10
  · exact group16_degree11
  · exact group16_degree12
  · exact group16_degree13
  · exact group16_degree14
  · exact group16_degree15
  · exact group16_degree16
  · exact group16_degree17
  · exact group16_degree18
  · exact group16_degree19
  · exact group16_degree20
  · exact group16_degree21
  · exact group16_degree22
  · exact group16_degree23
  · exact group16_degree24
  · exact group16_degree25
  · exact group16_degree26
  · exact group16_degree27
  · exact group16_degree28
  · exact group16_degree29
  · exact group16_degree30
  · exact group16_degree31
  · exact group16_degree32
  · exact group16_degree33
  · exact group16_degree34
  · exact group16_degree35
  · exact group16_degree36
  · exact group16_degree37
  · exact group16_degree38
  · exact group16_degree39
  · exact group16_degree40
  · exact group16_degree41
  · exact group16_degree42
  · exact group16_degree43
  · exact group16_degree44
  · exact group16_degree45
  · exact group16_degree46
  · exact group16_degree47

theorem group16_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient16 body16) z = eval k group16 z := by
  have he := eval_eq_of_fineParts 48 k group16_raw group16 z
    (fineBound_sound group16_raw_bound) (fineBound_sound group16_result_bound)
    group16_degrees
  change eval k (normalize group16_raw) z = eval k group16 z
  rw [eval_normalize]
  exact he

theorem coefficient16_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient16 (0:ℂ × ℂ)) coefficient16 := by
  convert Approximates.exactPolynomial 24 k coefficient16 using 1
  funext z
  simp [coefficient16,eval,evalTerm]

theorem evalContact_group16 (k s e : ℂ) :
    evalContact k phiGroup16 s e = eval k coefficient16 (0:ℂ × ℂ)*(s^16*(e⁻¹)^15) := by
  norm_num [phiGroup16,coefficient16,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group16_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup16 (halfSum z) (meanFunction z)) group16 := by
  have hb := ((halfPower16_approximates hk).mul hk (inversePower15_approximates hk hklog)).replacePolynomial
    (body16_eval k)
  have hh := ((coefficient16_approximates k).mul hk hb).replacePolynomial
    (group16_eval k)
  simpa only [evalContact_group16] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees
