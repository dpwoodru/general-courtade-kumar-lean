import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0229

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1832 : RatBall :=
  ⟨⟨87/320, -87/320⟩, 3/640⟩
def center1832 : GaussianRat :=
  ⟨19714711/100000000, -178023711/1000000000⟩
def contact1832 : RatBall := localContactBall tau1832 center1832
def work1832 : RoundedTauEval :=
  evalTau precision tau1832 contact1832 logTwoBall

theorem center_sq1832 : (center1832.re : ℝ)^2 +
    (center1832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1832 : work1832.theta.ok = true ∧
    work1832.jac.invOK = true ∧ acceptsUnitSq work1832.out = true := by
  norm_num [work1832, contact1832, tau1832, center1832, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1832 : CellCertificate where
  tauBall := tau1832
  contactCenter := center1832
  contactBall := contact1832
  work := work1832
  center_sq := center_sq1832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1832.1
  jac_ok := checks1832.2.1
  accepted := checks1832.2.2

def tau1833 : RatBall :=
  ⟨⟨17/64, -17/64⟩, 3/640⟩
def center1833 : GaussianRat :=
  ⟨12017011/62500000, -17442227/100000000⟩
def contact1833 : RatBall := localContactBall tau1833 center1833
def work1833 : RoundedTauEval :=
  evalTau precision tau1833 contact1833 logTwoBall

theorem center_sq1833 : (center1833.re : ℝ)^2 +
    (center1833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1833 : work1833.theta.ok = true ∧
    work1833.jac.invOK = true ∧ acceptsUnitSq work1833.out = true := by
  norm_num [work1833, contact1833, tau1833, center1833, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1833 : CellCertificate where
  tauBall := tau1833
  contactCenter := center1833
  contactBall := contact1833
  work := work1833
  center_sq := center_sq1833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1833.1
  jac_ok := checks1833.2.1
  accepted := checks1833.2.2

def tau1834 : RatBall :=
  ⟨⟨87/320, -17/64⟩, 3/640⟩
def center1834 : GaussianRat :=
  ⟨98252729/500000000, -34758949/200000000⟩
def contact1834 : RatBall := localContactBall tau1834 center1834
def work1834 : RoundedTauEval :=
  evalTau precision tau1834 contact1834 logTwoBall

theorem center_sq1834 : (center1834.re : ℝ)^2 +
    (center1834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1834 : work1834.theta.ok = true ∧
    work1834.jac.invOK = true ∧ acceptsUnitSq work1834.out = true := by
  norm_num [work1834, contact1834, tau1834, center1834, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1834 : CellCertificate where
  tauBall := tau1834
  contactCenter := center1834
  contactBall := contact1834
  work := work1834
  center_sq := center_sq1834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1834.1
  jac_ok := checks1834.2.1
  accepted := checks1834.2.2

def tau1835 : RatBall :=
  ⟨⟨89/320, -87/320⟩, 3/640⟩
def center1835 : GaussianRat :=
  ⟨201371579/1000000000, -177367859/1000000000⟩
def contact1835 : RatBall := localContactBall tau1835 center1835
def work1835 : RoundedTauEval :=
  evalTau precision tau1835 contact1835 logTwoBall

theorem center_sq1835 : (center1835.re : ℝ)^2 +
    (center1835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1835 : work1835.theta.ok = true ∧
    work1835.jac.invOK = true ∧ acceptsUnitSq work1835.out = true := by
  norm_num [work1835, contact1835, tau1835, center1835, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1835 : CellCertificate where
  tauBall := tau1835
  contactCenter := center1835
  contactBall := contact1835
  work := work1835
  center_sq := center_sq1835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1835.1
  jac_ok := checks1835.2.1
  accepted := checks1835.2.2

def tau1836 : RatBall :=
  ⟨⟨91/320, -87/320⟩, 3/640⟩
def center1836 : GaussianRat :=
  ⟨102788551/500000000, -176702417/1000000000⟩
def contact1836 : RatBall := localContactBall tau1836 center1836
def work1836 : RoundedTauEval :=
  evalTau precision tau1836 contact1836 logTwoBall

theorem center_sq1836 : (center1836.re : ℝ)^2 +
    (center1836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1836]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1836 : work1836.theta.ok = true ∧
    work1836.jac.invOK = true ∧ acceptsUnitSq work1836.out = true := by
  norm_num [work1836, contact1836, tau1836, center1836, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1836 : CellCertificate where
  tauBall := tau1836
  contactCenter := center1836
  contactBall := contact1836
  work := work1836
  center_sq := center_sq1836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1836.1
  jac_ok := checks1836.2.1
  accepted := checks1836.2.2

def tau1837 : RatBall :=
  ⟨⟨89/320, -17/64⟩, 3/640⟩
def center1837 : GaussianRat :=
  ⟨20072031/100000000, -86578791/500000000⟩
def contact1837 : RatBall := localContactBall tau1837 center1837
def work1837 : RoundedTauEval :=
  evalTau precision tau1837 contact1837 logTwoBall

theorem center_sq1837 : (center1837.re : ℝ)^2 +
    (center1837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1837 : work1837.theta.ok = true ∧
    work1837.jac.invOK = true ∧ acceptsUnitSq work1837.out = true := by
  norm_num [work1837, contact1837, tau1837, center1837, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1837 : CellCertificate where
  tauBall := tau1837
  contactCenter := center1837
  contactBall := contact1837
  work := work1837
  center_sq := center_sq1837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1837.1
  jac_ok := checks1837.2.1
  accepted := checks1837.2.2

def tau1838 : RatBall :=
  ⟨⟨91/320, -17/64⟩, 3/640⟩
def center1838 : GaussianRat :=
  ⟨102458249/500000000, -172511057/1000000000⟩
def contact1838 : RatBall := localContactBall tau1838 center1838
def work1838 : RoundedTauEval :=
  evalTau precision tau1838 contact1838 logTwoBall

theorem center_sq1838 : (center1838.re : ℝ)^2 +
    (center1838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1838 : work1838.theta.ok = true ∧
    work1838.jac.invOK = true ∧ acceptsUnitSq work1838.out = true := by
  norm_num [work1838, contact1838, tau1838, center1838, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1838 : CellCertificate where
  tauBall := tau1838
  contactCenter := center1838
  contactBall := contact1838
  work := work1838
  center_sq := center_sq1838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1838.1
  jac_ok := checks1838.2.1
  accepted := checks1838.2.2

def tau1839 : RatBall :=
  ⟨⟨93/320, -87/320⟩, 3/640⟩
def center1839 : GaussianRat :=
  ⟨1638777/7812500, -17602767/100000000⟩
def contact1839 : RatBall := localContactBall tau1839 center1839
def work1839 : RoundedTauEval :=
  evalTau precision tau1839 contact1839 logTwoBall

theorem center_sq1839 : (center1839.re : ℝ)^2 +
    (center1839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1839 : work1839.theta.ok = true ∧
    work1839.jac.invOK = true ∧ acceptsUnitSq work1839.out = true := by
  norm_num [work1839, contact1839, tau1839, center1839, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1839 : CellCertificate where
  tauBall := tau1839
  contactCenter := center1839
  contactBall := contact1839
  work := work1839
  center_sq := center_sq1839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1839.1
  jac_ok := checks1839.2.1
  accepted := checks1839.2.2

def cells : List CellCertificate := [cell1832, cell1833, cell1834, cell1835, cell1836, cell1837, cell1838, cell1839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0229
