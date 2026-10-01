import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0776 : RatBall :=
  ⟨⟨-63/160, 9/160⟩, 3/320⟩
def center0776 : GaussianRat :=
  ⟨-65046299/250000000, 6715607/200000000⟩
def contact0776 : RatBall := localContactBall tau0776 center0776
def work0776 : RoundedTauEval :=
  evalTau precision tau0776 contact0776 logTwoBall

theorem center_sq0776 : (center0776.re : ℝ)^2 +
    (center0776.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0776]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0776 : work0776.theta.ok = true ∧
    work0776.jac.invOK = true ∧ acceptsUnitSq work0776.out = true := by
  norm_num [work0776, contact0776, tau0776, center0776, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0776 : CellCertificate where
  tauBall := tau0776
  contactCenter := center0776
  contactBall := contact0776
  work := work0776
  center_sq := center_sq0776
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0776.1
  jac_ok := checks0776.2.1
  accepted := checks0776.2.2

def tau0777 : RatBall :=
  ⟨⟨-61/160, 9/160⟩, 3/320⟩
def center0777 : GaussianRat :=
  ⟨-252683709/1000000000, 6774897/200000000⟩
def contact0777 : RatBall := localContactBall tau0777 center0777
def work0777 : RoundedTauEval :=
  evalTau precision tau0777 contact0777 logTwoBall

theorem center_sq0777 : (center0777.re : ℝ)^2 +
    (center0777.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0777]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0777 : work0777.theta.ok = true ∧
    work0777.jac.invOK = true ∧ acceptsUnitSq work0777.out = true := by
  norm_num [work0777, contact0777, tau0777, center0777, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0777 : CellCertificate where
  tauBall := tau0777
  contactCenter := center0777
  contactBall := contact0777
  work := work0777
  center_sq := center_sq0777
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0777.1
  jac_ok := checks0777.2.1
  accepted := checks0777.2.2

def tau0778 : RatBall :=
  ⟨⟨-63/160, 11/160⟩, 3/320⟩
def center0778 : GaussianRat :=
  ⟨-260517353/1000000000, 1026213/25000000⟩
def contact0778 : RatBall := localContactBall tau0778 center0778
def work0778 : RoundedTauEval :=
  evalTau precision tau0778 contact0778 logTwoBall

theorem center_sq0778 : (center0778.re : ℝ)^2 +
    (center0778.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0778]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0778 : work0778.theta.ok = true ∧
    work0778.jac.invOK = true ∧ acceptsUnitSq work0778.out = true := by
  norm_num [work0778, contact0778, tau0778, center0778, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0778 : CellCertificate where
  tauBall := tau0778
  contactCenter := center0778
  contactBall := contact0778
  work := work0778
  center_sq := center_sq0778
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0778.1
  jac_ok := checks0778.2.1
  accepted := checks0778.2.2

def tau0779 : RatBall :=
  ⟨⟨-61/160, 11/160⟩, 3/320⟩
def center0779 : GaussianRat :=
  ⟨-25301093/100000000, 41411583/1000000000⟩
def contact0779 : RatBall := localContactBall tau0779 center0779
def work0779 : RoundedTauEval :=
  evalTau precision tau0779 contact0779 logTwoBall

theorem center_sq0779 : (center0779.re : ℝ)^2 +
    (center0779.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0779]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0779 : work0779.theta.ok = true ∧
    work0779.jac.invOK = true ∧ acceptsUnitSq work0779.out = true := by
  norm_num [work0779, contact0779, tau0779, center0779, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0779 : CellCertificate where
  tauBall := tau0779
  contactCenter := center0779
  contactBall := contact0779
  work := work0779
  center_sq := center_sq0779
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0779.1
  jac_ok := checks0779.2.1
  accepted := checks0779.2.2

def tau0780 : RatBall :=
  ⟨⟨-63/160, 13/160⟩, 3/320⟩
def center0780 : GaussianRat :=
  ⟨-260916819/1000000000, 48524207/1000000000⟩
def contact0780 : RatBall := localContactBall tau0780 center0780
def work0780 : RoundedTauEval :=
  evalTau precision tau0780 contact0780 logTwoBall

theorem center_sq0780 : (center0780.re : ℝ)^2 +
    (center0780.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0780]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0780 : work0780.theta.ok = true ∧
    work0780.jac.invOK = true ∧ acceptsUnitSq work0780.out = true := by
  norm_num [work0780, contact0780, tau0780, center0780, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0780 : CellCertificate where
  tauBall := tau0780
  contactCenter := center0780
  contactBall := contact0780
  work := work0780
  center_sq := center_sq0780
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0780.1
  jac_ok := checks0780.2.1
  accepted := checks0780.2.2

def tau0781 : RatBall :=
  ⟨⟨-61/160, 13/160⟩, 3/320⟩
def center0781 : GaussianRat :=
  ⟨-126702243/500000000, 6119291/125000000⟩
def contact0781 : RatBall := localContactBall tau0781 center0781
def work0781 : RoundedTauEval :=
  evalTau precision tau0781 contact0781 logTwoBall

theorem center_sq0781 : (center0781.re : ℝ)^2 +
    (center0781.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0781]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0781 : work0781.theta.ok = true ∧
    work0781.jac.invOK = true ∧ acceptsUnitSq work0781.out = true := by
  norm_num [work0781, contact0781, tau0781, center0781, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0781 : CellCertificate where
  tauBall := tau0781
  contactCenter := center0781
  contactBall := contact0781
  work := work0781
  center_sq := center_sq0781
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0781.1
  jac_ok := checks0781.2.1
  accepted := checks0781.2.2

def tau0782 : RatBall :=
  ⟨⟨-63/160, 3/32⟩, 3/320⟩
def center0782 : GaussianRat :=
  ⟨-65346019/250000000, 28003013/500000000⟩
def contact0782 : RatBall := localContactBall tau0782 center0782
def work0782 : RoundedTauEval :=
  evalTau precision tau0782 contact0782 logTwoBall

theorem center_sq0782 : (center0782.re : ℝ)^2 +
    (center0782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0782 : work0782.theta.ok = true ∧
    work0782.jac.invOK = true ∧ acceptsUnitSq work0782.out = true := by
  norm_num [work0782, contact0782, tau0782, center0782, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0782 : CellCertificate where
  tauBall := tau0782
  contactCenter := center0782
  contactBall := contact0782
  work := work0782
  center_sq := center_sq0782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0782.1
  jac_ok := checks0782.2.1
  accepted := checks0782.2.2

def tau0783 : RatBall :=
  ⟨⟨-61/160, 3/32⟩, 3/320⟩
def center0783 : GaussianRat :=
  ⟨-50772973/200000000, 14125933/250000000⟩
def contact0783 : RatBall := localContactBall tau0783 center0783
def work0783 : RoundedTauEval :=
  evalTau precision tau0783 contact0783 logTwoBall

theorem center_sq0783 : (center0783.re : ℝ)^2 +
    (center0783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0783 : work0783.theta.ok = true ∧
    work0783.jac.invOK = true ∧ acceptsUnitSq work0783.out = true := by
  norm_num [work0783, contact0783, tau0783, center0783, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0783 : CellCertificate where
  tauBall := tau0783
  contactCenter := center0783
  contactBall := contact0783
  work := work0783
  center_sq := center_sq0783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0783.1
  jac_ok := checks0783.2.1
  accepted := checks0783.2.2

def cells : List CellCertificate := [cell0776, cell0777, cell0778, cell0779, cell0780, cell0781, cell0782, cell0783]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097
