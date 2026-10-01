import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1824 : RatBall :=
  ⟨⟨89/320, -89/320⟩, 3/640⟩
def center1824 : GaussianRat :=
  ⟨40408359/200000000, -181587727/1000000000⟩
def contact1824 : RatBall := localContactBall tau1824 center1824
def work1824 : RoundedTauEval :=
  evalTau precision tau1824 contact1824 logTwoBall

theorem center_sq1824 : (center1824.re : ℝ)^2 +
    (center1824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1824 : work1824.theta.ok = true ∧
    work1824.jac.invOK = true ∧ acceptsUnitSq work1824.out = true := by
  norm_num [work1824, contact1824, tau1824, center1824, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1824 : CellCertificate where
  tauBall := tau1824
  contactCenter := center1824
  contactBall := contact1824
  work := work1824
  center_sq := center_sq1824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1824.1
  jac_ok := checks1824.2.1
  accepted := checks1824.2.2

def tau1825 : RatBall :=
  ⟨⟨91/320, -89/320⟩, 3/640⟩
def center1825 : GaussianRat :=
  ⟨103128439/500000000, -180903081/1000000000⟩
def contact1825 : RatBall := localContactBall tau1825 center1825
def work1825 : RoundedTauEval :=
  evalTau precision tau1825 contact1825 logTwoBall

theorem center_sq1825 : (center1825.re : ℝ)^2 +
    (center1825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1825 : work1825.theta.ok = true ∧
    work1825.jac.invOK = true ∧ acceptsUnitSq work1825.out = true := by
  norm_num [work1825, contact1825, tau1825, center1825, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1825 : CellCertificate where
  tauBall := tau1825
  contactCenter := center1825
  contactBall := contact1825
  work := work1825
  center_sq := center_sq1825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1825.1
  jac_ok := checks1825.2.1
  accepted := checks1825.2.2

def tau1826 : RatBall :=
  ⟨⟨93/320, -89/320⟩, 3/640⟩
def center1826 : GaussianRat :=
  ⟨84181/400000, -180208911/1000000000⟩
def contact1826 : RatBall := localContactBall tau1826 center1826
def work1826 : RoundedTauEval :=
  evalTau precision tau1826 contact1826 logTwoBall

theorem center_sq1826 : (center1826.re : ℝ)^2 +
    (center1826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1826 : work1826.theta.ok = true ∧
    work1826.jac.invOK = true ∧ acceptsUnitSq work1826.out = true := by
  norm_num [work1826, contact1826, tau1826, center1826, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1826 : CellCertificate where
  tauBall := tau1826
  contactCenter := center1826
  contactBall := contact1826
  work := work1826
  center_sq := center_sq1826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1826.1
  jac_ok := checks1826.2.1
  accepted := checks1826.2.2

def tau1827 : RatBall :=
  ⟨⟨81/320, -87/320⟩, 3/640⟩
def center1827 : GaussianRat :=
  ⟨9218121/50000000, -179930859/1000000000⟩
def contact1827 : RatBall := localContactBall tau1827 center1827
def work1827 : RoundedTauEval :=
  evalTau precision tau1827 contact1827 logTwoBall

theorem center_sq1827 : (center1827.re : ℝ)^2 +
    (center1827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1827 : work1827.theta.ok = true ∧
    work1827.jac.invOK = true ∧ acceptsUnitSq work1827.out = true := by
  norm_num [work1827, contact1827, tau1827, center1827, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1827 : CellCertificate where
  tauBall := tau1827
  contactCenter := center1827
  contactBall := contact1827
  work := work1827
  center_sq := center_sq1827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1827.1
  jac_ok := checks1827.2.1
  accepted := checks1827.2.2

def tau1828 : RatBall :=
  ⟨⟨83/320, -87/320⟩, 3/640⟩
def center1828 : GaussianRat :=
  ⟨188642281/1000000000, -22413187/125000000⟩
def contact1828 : RatBall := localContactBall tau1828 center1828
def work1828 : RoundedTauEval :=
  evalTau precision tau1828 contact1828 logTwoBall

theorem center_sq1828 : (center1828.re : ℝ)^2 +
    (center1828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1828 : work1828.theta.ok = true ∧
    work1828.jac.invOK = true ∧ acceptsUnitSq work1828.out = true := by
  norm_num [work1828, contact1828, tau1828, center1828, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1828 : CellCertificate where
  tauBall := tau1828
  contactCenter := center1828
  contactBall := contact1828
  work := work1828
  center_sq := center_sq1828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1828.1
  jac_ok := checks1828.2.1
  accepted := checks1828.2.2

def tau1829 : RatBall :=
  ⟨⟨81/320, -17/64⟩, 3/640⟩
def center1829 : GaussianRat :=
  ⟨36750261/200000000, -1756473/10000000⟩
def contact1829 : RatBall := localContactBall tau1829 center1829
def work1829 : RoundedTauEval :=
  evalTau precision tau1829 contact1829 logTwoBall

theorem center_sq1829 : (center1829.re : ℝ)^2 +
    (center1829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1829 : work1829.theta.ok = true ∧
    work1829.jac.invOK = true ∧ acceptsUnitSq work1829.out = true := by
  norm_num [work1829, contact1829, tau1829, center1829, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1829 : CellCertificate where
  tauBall := tau1829
  contactCenter := center1829
  contactBall := contact1829
  work := work1829
  center_sq := center_sq1829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1829.1
  jac_ok := checks1829.2.1
  accepted := checks1829.2.2

def tau1830 : RatBall :=
  ⟨⟨83/320, -17/64⟩, 3/640⟩
def center1830 : GaussianRat :=
  ⟨188020707/1000000000, -4375997/25000000⟩
def contact1830 : RatBall := localContactBall tau1830 center1830
def work1830 : RoundedTauEval :=
  evalTau precision tau1830 contact1830 logTwoBall

theorem center_sq1830 : (center1830.re : ℝ)^2 +
    (center1830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1830 : work1830.theta.ok = true ∧
    work1830.jac.invOK = true ∧ acceptsUnitSq work1830.out = true := by
  norm_num [work1830, contact1830, tau1830, center1830, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1830 : CellCertificate where
  tauBall := tau1830
  contactCenter := center1830
  contactBall := contact1830
  work := work1830
  center_sq := center_sq1830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1830.1
  jac_ok := checks1830.2.1
  accepted := checks1830.2.2

def tau1831 : RatBall :=
  ⟨⟨17/64, -87/320⟩, 3/640⟩
def center1831 : GaussianRat :=
  ⟨192903929/1000000000, -35733937/200000000⟩
def contact1831 : RatBall := localContactBall tau1831 center1831
def work1831 : RoundedTauEval :=
  evalTau precision tau1831 contact1831 logTwoBall

theorem center_sq1831 : (center1831.re : ℝ)^2 +
    (center1831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1831 : work1831.theta.ok = true ∧
    work1831.jac.invOK = true ∧ acceptsUnitSq work1831.out = true := by
  norm_num [work1831, contact1831, tau1831, center1831, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1831 : CellCertificate where
  tauBall := tau1831
  contactCenter := center1831
  contactBall := contact1831
  work := work1831
  center_sq := center_sq1831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1831.1
  jac_ok := checks1831.2.1
  accepted := checks1831.2.2

def cells : List CellCertificate := [cell1824, cell1825, cell1826, cell1827, cell1828, cell1829, cell1830, cell1831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228
