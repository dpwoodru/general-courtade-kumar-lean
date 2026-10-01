import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0104 : RatBall :=
  ⟨⟨-17/80, -1/16⟩, 3/160⟩
def center0104 : GaussianRat :=
  ⟨-29119789/200000000, -10355411/250000000⟩
def contact0104 : RatBall := localContactBall tau0104 center0104
def work0104 : RoundedTauEval :=
  evalTau precision tau0104 contact0104 logTwoBall

theorem center_sq0104 : (center0104.re : ℝ)^2 +
    (center0104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0104 : work0104.theta.ok = true ∧
    work0104.jac.invOK = true ∧ acceptsUnitSq work0104.out = true := by
  norm_num [work0104, contact0104, tau0104, center0104, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0104 : CellCertificate where
  tauBall := tau0104
  contactCenter := center0104
  contactBall := contact0104
  work := work0104
  center_sq := center_sq0104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0104.1
  jac_ok := checks0104.2.1
  accepted := checks0104.2.2

def tau0105 : RatBall :=
  ⟨⟨-23/80, -3/80⟩, 3/160⟩
def center0105 : GaussianRat :=
  ⟨-4852301/25000000, -23940531/1000000000⟩
def contact0105 : RatBall := localContactBall tau0105 center0105
def work0105 : RoundedTauEval :=
  evalTau precision tau0105 contact0105 logTwoBall

theorem center_sq0105 : (center0105.re : ℝ)^2 +
    (center0105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0105 : work0105.theta.ok = true ∧
    work0105.jac.invOK = true ∧ acceptsUnitSq work0105.out = true := by
  norm_num [work0105, contact0105, tau0105, center0105, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0105 : CellCertificate where
  tauBall := tau0105
  contactCenter := center0105
  contactBall := contact0105
  work := work0105
  center_sq := center_sq0105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0105.1
  jac_ok := checks0105.2.1
  accepted := checks0105.2.2

def tau0106 : RatBall :=
  ⟨⟨-21/80, -3/80⟩, 3/160⟩
def center0106 : GaussianRat :=
  ⟨-89006593/500000000, -4852281/200000000⟩
def contact0106 : RatBall := localContactBall tau0106 center0106
def work0106 : RoundedTauEval :=
  evalTau precision tau0106 contact0106 logTwoBall

theorem center_sq0106 : (center0106.re : ℝ)^2 +
    (center0106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0106 : work0106.theta.ok = true ∧
    work0106.jac.invOK = true ∧ acceptsUnitSq work0106.out = true := by
  norm_num [work0106, contact0106, tau0106, center0106, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0106 : CellCertificate where
  tauBall := tau0106
  contactCenter := center0106
  contactBall := contact0106
  work := work0106
  center_sq := center_sq0106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0106.1
  jac_ok := checks0106.2.1
  accepted := checks0106.2.2

def tau0107 : RatBall :=
  ⟨⟨-23/80, -1/80⟩, 3/160⟩
def center0107 : GaussianRat :=
  ⟨-7754861/40000000, -3988989/500000000⟩
def contact0107 : RatBall := localContactBall tau0107 center0107
def work0107 : RoundedTauEval :=
  evalTau precision tau0107 contact0107 logTwoBall

theorem center_sq0107 : (center0107.re : ℝ)^2 +
    (center0107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0107 : work0107.theta.ok = true ∧
    work0107.jac.invOK = true ∧ acceptsUnitSq work0107.out = true := by
  norm_num [work0107, contact0107, tau0107, center0107, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0107 : CellCertificate where
  tauBall := tau0107
  contactCenter := center0107
  contactBall := contact0107
  work := work0107
  center_sq := center_sq0107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0107.1
  jac_ok := checks0107.2.1
  accepted := checks0107.2.2

def tau0108 : RatBall :=
  ⟨⟨-21/80, -1/80⟩, 3/160⟩
def center0108 : GaussianRat :=
  ⟨-4445163/25000000, -8084719/1000000000⟩
def contact0108 : RatBall := localContactBall tau0108 center0108
def work0108 : RoundedTauEval :=
  evalTau precision tau0108 contact0108 logTwoBall

theorem center_sq0108 : (center0108.re : ℝ)^2 +
    (center0108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0108 : work0108.theta.ok = true ∧
    work0108.jac.invOK = true ∧ acceptsUnitSq work0108.out = true := by
  norm_num [work0108, contact0108, tau0108, center0108, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0108 : CellCertificate where
  tauBall := tau0108
  contactCenter := center0108
  contactBall := contact0108
  work := work0108
  center_sq := center_sq0108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0108.1
  jac_ok := checks0108.2.1
  accepted := checks0108.2.2

def tau0109 : RatBall :=
  ⟨⟨-3/16, -3/16⟩, 3/160⟩
def center0109 : GaussianRat :=
  ⟨-132989007/1000000000, -15833617/125000000⟩
def contact0109 : RatBall := localContactBall tau0109 center0109
def work0109 : RoundedTauEval :=
  evalTau precision tau0109 contact0109 logTwoBall

theorem center_sq0109 : (center0109.re : ℝ)^2 +
    (center0109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0109 : work0109.theta.ok = true ∧
    work0109.jac.invOK = true ∧ acceptsUnitSq work0109.out = true := by
  norm_num [work0109, contact0109, tau0109, center0109, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0109 : CellCertificate where
  tauBall := tau0109
  contactCenter := center0109
  contactBall := contact0109
  work := work0109
  center_sq := center_sq0109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0109.1
  jac_ok := checks0109.2.1
  accepted := checks0109.2.2

def tau0110 : RatBall :=
  ⟨⟨-13/80, -3/16⟩, 3/160⟩
def center0110 : GaussianRat :=
  ⟨-115659239/1000000000, -127856533/1000000000⟩
def contact0110 : RatBall := localContactBall tau0110 center0110
def work0110 : RoundedTauEval :=
  evalTau precision tau0110 contact0110 logTwoBall

theorem center_sq0110 : (center0110.re : ℝ)^2 +
    (center0110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0110 : work0110.theta.ok = true ∧
    work0110.jac.invOK = true ∧ acceptsUnitSq work0110.out = true := by
  norm_num [work0110, contact0110, tau0110, center0110, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0110 : CellCertificate where
  tauBall := tau0110
  contactCenter := center0110
  contactBall := contact0110
  work := work0110
  center_sq := center_sq0110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0110.1
  jac_ok := checks0110.2.1
  accepted := checks0110.2.2

def tau0111 : RatBall :=
  ⟨⟨-3/16, -13/80⟩, 3/160⟩
def center0111 : GaussianRat :=
  ⟨-131822371/1000000000, -13687313/125000000⟩
def contact0111 : RatBall := localContactBall tau0111 center0111
def work0111 : RoundedTauEval :=
  evalTau precision tau0111 contact0111 logTwoBall

theorem center_sq0111 : (center0111.re : ℝ)^2 +
    (center0111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0111 : work0111.theta.ok = true ∧
    work0111.jac.invOK = true ∧ acceptsUnitSq work0111.out = true := by
  norm_num [work0111, contact0111, tau0111, center0111, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0111 : CellCertificate where
  tauBall := tau0111
  contactCenter := center0111
  contactBall := contact0111
  work := work0111
  center_sq := center_sq0111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0111.1
  jac_ok := checks0111.2.1
  accepted := checks0111.2.2

def cells : List CellCertificate := [cell0104, cell0105, cell0106, cell0107, cell0108, cell0109, cell0110, cell0111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013
