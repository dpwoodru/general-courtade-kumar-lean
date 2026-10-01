import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0064 : RatBall :=
  ⟨⟨-7/80, -19/80⟩, 3/160⟩
def center0064 : GaussianRat :=
  ⟨-32100469/500000000, -83247331/500000000⟩
def contact0064 : RatBall := localContactBall tau0064 center0064
def work0064 : RoundedTauEval :=
  evalTau precision tau0064 contact0064 logTwoBall

theorem center_sq0064 : (center0064.re : ℝ)^2 +
    (center0064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0064 : work0064.theta.ok = true ∧
    work0064.jac.invOK = true ∧ acceptsUnitSq work0064.out = true := by
  norm_num [work0064, contact0064, tau0064, center0064, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0064 : CellCertificate where
  tauBall := tau0064
  contactCenter := center0064
  contactBall := contact0064
  work := work0064
  center_sq := center_sq0064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0064.1
  jac_ok := checks0064.2.1
  accepted := checks0064.2.2

def tau0065 : RatBall :=
  ⟨⟨-1/16, -19/80⟩, 3/160⟩
def center0065 : GaussianRat :=
  ⟨-45935893/1000000000, -836037/5000000⟩
def contact0065 : RatBall := localContactBall tau0065 center0065
def work0065 : RoundedTauEval :=
  evalTau precision tau0065 contact0065 logTwoBall

theorem center_sq0065 : (center0065.re : ℝ)^2 +
    (center0065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0065 : work0065.theta.ok = true ∧
    work0065.jac.invOK = true ∧ acceptsUnitSq work0065.out = true := by
  norm_num [work0065, contact0065, tau0065, center0065, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0065 : CellCertificate where
  tauBall := tau0065
  contactCenter := center0065
  contactBall := contact0065
  work := work0065
  center_sq := center_sq0065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0065.1
  jac_ok := checks0065.2.1
  accepted := checks0065.2.2

def tau0066 : RatBall :=
  ⟨⟨-7/80, -17/80⟩, 3/160⟩
def center0066 : GaussianRat :=
  ⟨-31712973/500000000, -37096923/250000000⟩
def contact0066 : RatBall := localContactBall tau0066 center0066
def work0066 : RoundedTauEval :=
  evalTau precision tau0066 contact0066 logTwoBall

theorem center_sq0066 : (center0066.re : ℝ)^2 +
    (center0066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0066 : work0066.theta.ok = true ∧
    work0066.jac.invOK = true ∧ acceptsUnitSq work0066.out = true := by
  norm_num [work0066, contact0066, tau0066, center0066, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0066 : CellCertificate where
  tauBall := tau0066
  contactCenter := center0066
  contactBall := contact0066
  work := work0066
  center_sq := center_sq0066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0066.1
  jac_ok := checks0066.2.1
  accepted := checks0066.2.2

def tau0067 : RatBall :=
  ⟨⟨-1/16, -17/80⟩, 3/160⟩
def center0067 : GaussianRat :=
  ⟨-22688687/500000000, -149010417/1000000000⟩
def contact0067 : RatBall := localContactBall tau0067 center0067
def work0067 : RoundedTauEval :=
  evalTau precision tau0067 contact0067 logTwoBall

theorem center_sq0067 : (center0067.re : ℝ)^2 +
    (center0067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0067 : work0067.theta.ok = true ∧
    work0067.jac.invOK = true ∧ acceptsUnitSq work0067.out = true := by
  norm_num [work0067, contact0067, tau0067, center0067, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0067 : CellCertificate where
  tauBall := tau0067
  contactCenter := center0067
  contactBall := contact0067
  work := work0067
  center_sq := center_sq0067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0067.1
  jac_ok := checks0067.2.1
  accepted := checks0067.2.2

def tau0068 : RatBall :=
  ⟨⟨-3/80, -19/80⟩, 3/160⟩
def center0068 : GaussianRat :=
  ⟨-551859/20000000, -167686167/1000000000⟩
def contact0068 : RatBall := localContactBall tau0068 center0068
def work0068 : RoundedTauEval :=
  evalTau precision tau0068 contact0068 logTwoBall

theorem center_sq0068 : (center0068.re : ℝ)^2 +
    (center0068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0068 : work0068.theta.ok = true ∧
    work0068.jac.invOK = true ∧ acceptsUnitSq work0068.out = true := by
  norm_num [work0068, contact0068, tau0068, center0068, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0068 : CellCertificate where
  tauBall := tau0068
  contactCenter := center0068
  contactBall := contact0068
  work := work0068
  center_sq := center_sq0068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0068.1
  jac_ok := checks0068.2.1
  accepted := checks0068.2.2

def tau0069 : RatBall :=
  ⟨⟨-1/80, -19/80⟩, 3/160⟩
def center0069 : GaussianRat :=
  ⟨-1150363/125000000, -41981661/250000000⟩
def contact0069 : RatBall := localContactBall tau0069 center0069
def work0069 : RoundedTauEval :=
  evalTau precision tau0069 contact0069 logTwoBall

theorem center_sq0069 : (center0069.re : ℝ)^2 +
    (center0069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0069 : work0069.theta.ok = true ∧
    work0069.jac.invOK = true ∧ acceptsUnitSq work0069.out = true := by
  norm_num [work0069, contact0069, tau0069, center0069, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0069 : CellCertificate where
  tauBall := tau0069
  contactCenter := center0069
  contactBall := contact0069
  work := work0069
  center_sq := center_sq0069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0069.1
  jac_ok := checks0069.2.1
  accepted := checks0069.2.2

def tau0070 : RatBall :=
  ⟨⟨-3/80, -17/80⟩, 3/160⟩
def center0070 : GaussianRat :=
  ⟨-13627917/500000000, -149428611/1000000000⟩
def contact0070 : RatBall := localContactBall tau0070 center0070
def work0070 : RoundedTauEval :=
  evalTau precision tau0070 contact0070 logTwoBall

theorem center_sq0070 : (center0070.re : ℝ)^2 +
    (center0070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0070 : work0070.theta.ok = true ∧
    work0070.jac.invOK = true ∧ acceptsUnitSq work0070.out = true := by
  norm_num [work0070, contact0070, tau0070, center0070, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0070 : CellCertificate where
  tauBall := tau0070
  contactCenter := center0070
  contactBall := contact0070
  work := work0070
  center_sq := center_sq0070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0070.1
  jac_ok := checks0070.2.1
  accepted := checks0070.2.2

def tau0071 : RatBall :=
  ⟨⟨-1/80, -17/80⟩, 3/160⟩
def center0071 : GaussianRat :=
  ⟨-2272549/250000000, -14963863/100000000⟩
def contact0071 : RatBall := localContactBall tau0071 center0071
def work0071 : RoundedTauEval :=
  evalTau precision tau0071 contact0071 logTwoBall

theorem center_sq0071 : (center0071.re : ℝ)^2 +
    (center0071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0071 : work0071.theta.ok = true ∧
    work0071.jac.invOK = true ∧ acceptsUnitSq work0071.out = true := by
  norm_num [work0071, contact0071, tau0071, center0071, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0071 : CellCertificate where
  tauBall := tau0071
  contactCenter := center0071
  contactBall := contact0071
  work := work0071
  center_sq := center_sq0071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0071.1
  jac_ok := checks0071.2.1
  accepted := checks0071.2.2

def cells : List CellCertificate := [cell0064, cell0065, cell0066, cell0067, cell0068, cell0069, cell0070, cell0071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008
