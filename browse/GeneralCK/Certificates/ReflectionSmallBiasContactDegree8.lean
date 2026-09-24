import GeneralCK.Certificates.ReflectionSmallBiasContactDegree8Checks1
import GeneralCK.Certificates.ReflectionSmallBiasContactDegree8Checks2

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body8_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d body8_raw) (finePart d body8) = true := by
  interval_cases d
  · exact body8_degree0
  · exact body8_degree1
  · exact body8_degree2
  · exact body8_degree3
  · exact body8_degree4
  · exact body8_degree5
  · exact body8_degree6
  · exact body8_degree7
  · exact body8_degree8
  · exact body8_degree9
  · exact body8_degree10
  · exact body8_degree11
  · exact body8_degree12
  · exact body8_degree13
  · exact body8_degree14
  · exact body8_degree15
  · exact body8_degree16
  · exact body8_degree17
  · exact body8_degree18
  · exact body8_degree19
  · exact body8_degree20
  · exact body8_degree21
  · exact body8_degree22
  · exact body8_degree23
  · exact body8_degree24
  · exact body8_degree25
  · exact body8_degree26
  · exact body8_degree27
  · exact body8_degree28
  · exact body8_degree29
  · exact body8_degree30
  · exact body8_degree31
  · exact body8_degree32
  · exact body8_degree33
  · exact body8_degree34
  · exact body8_degree35
  · exact body8_degree36
  · exact body8_degree37
  · exact body8_degree38
  · exact body8_degree39
  · exact body8_degree40
  · exact body8_degree41
  · exact body8_degree42
  · exact body8_degree43
  · exact body8_degree44
  · exact body8_degree45
  · exact body8_degree46
  · exact body8_degree47

theorem body8_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower8 inversePower7) z = eval k body8 z := by
  have he := eval_eq_of_fineParts 48 k body8_raw body8 z
    (fineBound_sound body8_raw_bound) (fineBound_sound body8_result_bound)
    body8_degrees
  change eval k (normalize body8_raw) z = eval k body8 z
  rw [eval_normalize]
  exact he

theorem group8_degrees (d : ℕ) (hd : d<48) :
    equalityCheck (finePart d group8_raw) (finePart d group8) = true := by
  interval_cases d
  · exact group8_degree0
  · exact group8_degree1
  · exact group8_degree2
  · exact group8_degree3
  · exact group8_degree4
  · exact group8_degree5
  · exact group8_degree6
  · exact group8_degree7
  · exact group8_degree8
  · exact group8_degree9
  · exact group8_degree10
  · exact group8_degree11
  · exact group8_degree12
  · exact group8_degree13
  · exact group8_degree14
  · exact group8_degree15
  · exact group8_degree16
  · exact group8_degree17
  · exact group8_degree18
  · exact group8_degree19
  · exact group8_degree20
  · exact group8_degree21
  · exact group8_degree22
  · exact group8_degree23
  · exact group8_degree24
  · exact group8_degree25
  · exact group8_degree26
  · exact group8_degree27
  · exact group8_degree28
  · exact group8_degree29
  · exact group8_degree30
  · exact group8_degree31
  · exact group8_degree32
  · exact group8_degree33
  · exact group8_degree34
  · exact group8_degree35
  · exact group8_degree36
  · exact group8_degree37
  · exact group8_degree38
  · exact group8_degree39
  · exact group8_degree40
  · exact group8_degree41
  · exact group8_degree42
  · exact group8_degree43
  · exact group8_degree44
  · exact group8_degree45
  · exact group8_degree46
  · exact group8_degree47

theorem group8_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient8 body8) z = eval k group8 z := by
  have he := eval_eq_of_fineParts 48 k group8_raw group8 z
    (fineBound_sound group8_raw_bound) (fineBound_sound group8_result_bound)
    group8_degrees
  change eval k (normalize group8_raw) z = eval k group8 z
  rw [eval_normalize]
  exact he

theorem coefficient8_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient8 (0:ℂ × ℂ)) coefficient8 := by
  convert Approximates.exactPolynomial 24 k coefficient8 using 1
  funext z
  simp [coefficient8,eval,evalTerm]

theorem evalContact_group8 (k s e : ℂ) :
    evalContact k phiGroup8 s e = eval k coefficient8 (0:ℂ × ℂ)*(s^8*(e⁻¹)^7) := by
  norm_num [phiGroup8,coefficient8,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group8_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup8 (halfSum z) (meanFunction z)) group8 := by
  have hb := ((halfPower8_approximates hk).mul hk (inversePower7_approximates hk hklog)).replacePolynomial
    (body8_eval k)
  have hh := ((coefficient8_approximates k).mul hk hb).replacePolynomial
    (group8_eval k)
  simpa only [evalContact_group8] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees
