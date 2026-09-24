import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace GeneralCK.Reflection.HighBiasRational

theorem case1_bound {a b c B q u : ℝ}
    (ha : (999/1000:ℝ)≤a) (hb : (1/2:ℝ)≤b) (hc : (1/2:ℝ)≤c)
    (hB : (69/100:ℝ)≤B) (hq0 : 0≤q) (hq1 : q≤1/2)
    (_hu0 : 0≤u) (hu1 : u≤4/125) :
    2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B)<1/2 := by
  have h : 2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B) ≤
      2*(1/2:ℝ)^2/((999/1000)^3*(1/2)*(999/1000+1/2)*(1+1/2)^2)+
      (4/125)/((999/1000)^3*(1/2)*(1+999/1000)*(1+1/2)*(69/100)) := by
    gcongr
  exact h.trans_lt (by norm_num)

theorem case2_bound {a b c B q u : ℝ}
    (ha : (999/1000:ℝ)≤a) (hb : (109/125:ℝ)≤b) (hc : (121/125:ℝ)≤c)
    (hB : (69/40:ℝ)≤B) (hq0 : 0≤q) (hq1 : q≤1)
    (_hu0 : 0≤u) (hu1 : u≤1) :
    2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B)<1/2 := by
  have h : 2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B) ≤
      2*(1:ℝ)^2/((999/1000)^3*(109/125)*(999/1000+109/125)*(1+121/125)^2)+
      1/((999/1000)^3*(109/125)*(1+999/1000)*(1+121/125)*(69/40)) := by
    gcongr
  exact h.trans_lt (by norm_num)

end GeneralCK.Reflection.HighBiasRational
