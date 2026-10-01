import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1664 : RatBall :=
  ⟨⟨43/320, -111/320⟩, 3/640⟩
def center1664 : GaussianRat :=
  ⟨21054511/200000000, -122778933/500000000⟩
def contact1664 : RatBall := localContactBall tau1664 center1664
def work1664 : RoundedTauEval :=
  evalTau precision tau1664 contact1664 logTwoBall

theorem center_sq1664 : (center1664.re : ℝ)^2 +
    (center1664.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1664]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1664 : work1664.theta.ok = true ∧
    work1664.jac.invOK = true ∧ acceptsUnitSq work1664.out = true := by
  norm_num [work1664, contact1664, tau1664, center1664, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1664 : CellCertificate where
  tauBall := tau1664
  contactCenter := center1664
  contactBall := contact1664
  work := work1664
  center_sq := center_sq1664
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1664.1
  jac_ok := checks1664.2.1
  accepted := checks1664.2.2

def tau1665 : RatBall :=
  ⟨⟨41/320, -109/320⟩, 3/640⟩
def center1665 : GaussianRat :=
  ⟨6249053/62500000, -241270351/1000000000⟩
def contact1665 : RatBall := localContactBall tau1665 center1665
def work1665 : RoundedTauEval :=
  evalTau precision tau1665 contact1665 logTwoBall

theorem center_sq1665 : (center1665.re : ℝ)^2 +
    (center1665.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1665]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1665 : work1665.theta.ok = true ∧
    work1665.jac.invOK = true ∧ acceptsUnitSq work1665.out = true := by
  norm_num [work1665, contact1665, tau1665, center1665, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1665 : CellCertificate where
  tauBall := tau1665
  contactCenter := center1665
  contactBall := contact1665
  work := work1665
  center_sq := center_sq1665
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1665.1
  jac_ok := checks1665.2.1
  accepted := checks1665.2.2

def tau1666 : RatBall :=
  ⟨⟨43/320, -109/320⟩, 3/640⟩
def center1666 : GaussianRat :=
  ⟨26190451/250000000, -3762143/15625000⟩
def contact1666 : RatBall := localContactBall tau1666 center1666
def work1666 : RoundedTauEval :=
  evalTau precision tau1666 contact1666 logTwoBall

theorem center_sq1666 : (center1666.re : ℝ)^2 +
    (center1666.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1666]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1666 : work1666.theta.ok = true ∧
    work1666.jac.invOK = true ∧ acceptsUnitSq work1666.out = true := by
  norm_num [work1666, contact1666, tau1666, center1666, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1666 : CellCertificate where
  tauBall := tau1666
  contactCenter := center1666
  contactBall := contact1666
  work := work1666
  center_sq := center_sq1666
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1666.1
  jac_ok := checks1666.2.1
  accepted := checks1666.2.2

def tau1667 : RatBall :=
  ⟨⟨9/64, -111/320⟩, 3/640⟩
def center1667 : GaussianRat :=
  ⟨4402271/40000000, -122514671/500000000⟩
def contact1667 : RatBall := localContactBall tau1667 center1667
def work1667 : RoundedTauEval :=
  evalTau precision tau1667 contact1667 logTwoBall

theorem center_sq1667 : (center1667.re : ℝ)^2 +
    (center1667.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1667]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1667 : work1667.theta.ok = true ∧
    work1667.jac.invOK = true ∧ acceptsUnitSq work1667.out = true := by
  norm_num [work1667, contact1667, tau1667, center1667, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1667 : CellCertificate where
  tauBall := tau1667
  contactCenter := center1667
  contactBall := contact1667
  work := work1667
  center_sq := center_sq1667
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1667.1
  jac_ok := checks1667.2.1
  accepted := checks1667.2.2

def tau1668 : RatBall :=
  ⟨⟨47/320, -111/320⟩, 3/640⟩
def center1668 : GaussianRat :=
  ⟨57413127/500000000, -244479579/1000000000⟩
def contact1668 : RatBall := localContactBall tau1668 center1668
def work1668 : RoundedTauEval :=
  evalTau precision tau1668 contact1668 logTwoBall

theorem center_sq1668 : (center1668.re : ℝ)^2 +
    (center1668.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1668]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1668 : work1668.theta.ok = true ∧
    work1668.jac.invOK = true ∧ acceptsUnitSq work1668.out = true := by
  norm_num [work1668, contact1668, tau1668, center1668, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1668 : CellCertificate where
  tauBall := tau1668
  contactCenter := center1668
  contactBall := contact1668
  work := work1668
  center_sq := center_sq1668
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1668.1
  jac_ok := checks1668.2.1
  accepted := checks1668.2.2

def tau1669 : RatBall :=
  ⟨⟨9/64, -109/320⟩, 3/640⟩
def center1669 : GaussianRat :=
  ⟨109524891/1000000000, -240262931/1000000000⟩
def contact1669 : RatBall := localContactBall tau1669 center1669
def work1669 : RoundedTauEval :=
  evalTau precision tau1669 contact1669 logTwoBall

theorem center_sq1669 : (center1669.re : ℝ)^2 +
    (center1669.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1669]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1669 : work1669.theta.ok = true ∧
    work1669.jac.invOK = true ∧ acceptsUnitSq work1669.out = true := by
  norm_num [work1669, contact1669, tau1669, center1669, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1669 : CellCertificate where
  tauBall := tau1669
  contactCenter := center1669
  contactBall := contact1669
  work := work1669
  center_sq := center_sq1669
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1669.1
  jac_ok := checks1669.2.1
  accepted := checks1669.2.2

def tau1670 : RatBall :=
  ⟨⟨47/320, -109/320⟩, 3/640⟩
def center1670 : GaussianRat :=
  ⟨3571049/31250000, -239728011/1000000000⟩
def contact1670 : RatBall := localContactBall tau1670 center1670
def work1670 : RoundedTauEval :=
  evalTau precision tau1670 contact1670 logTwoBall

theorem center_sq1670 : (center1670.re : ℝ)^2 +
    (center1670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1670 : work1670.theta.ok = true ∧
    work1670.jac.invOK = true ∧ acceptsUnitSq work1670.out = true := by
  norm_num [work1670, contact1670, tau1670, center1670, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1670 : CellCertificate where
  tauBall := tau1670
  contactCenter := center1670
  contactBall := contact1670
  work := work1670
  center_sq := center_sq1670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1670.1
  jac_ok := checks1670.2.1
  accepted := checks1670.2.2

def tau1671 : RatBall :=
  ⟨⟨41/320, -107/320⟩, 3/640⟩
def center1671 : GaussianRat :=
  ⟨99508871/1000000000, -236497219/1000000000⟩
def contact1671 : RatBall := localContactBall tau1671 center1671
def work1671 : RoundedTauEval :=
  evalTau precision tau1671 contact1671 logTwoBall

theorem center_sq1671 : (center1671.re : ℝ)^2 +
    (center1671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1671 : work1671.theta.ok = true ∧
    work1671.jac.invOK = true ∧ acceptsUnitSq work1671.out = true := by
  norm_num [work1671, contact1671, tau1671, center1671, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1671 : CellCertificate where
  tauBall := tau1671
  contactCenter := center1671
  contactBall := contact1671
  work := work1671
  center_sq := center_sq1671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1671.1
  jac_ok := checks1671.2.1
  accepted := checks1671.2.2

def cells : List CellCertificate := [cell1664, cell1665, cell1666, cell1667, cell1668, cell1669, cell1670, cell1671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208
