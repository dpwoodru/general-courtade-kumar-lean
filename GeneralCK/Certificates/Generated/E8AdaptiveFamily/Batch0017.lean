import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0017

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0136 : RatBall :=
  ⟨⟨7/80, -19/80⟩, 3/160⟩
def center0136 : GaussianRat :=
  ⟨32100469/500000000, -83247331/500000000⟩
def contact0136 : RatBall := localContactBall tau0136 center0136
def work0136 : RoundedTauEval :=
  evalTau precision tau0136 contact0136 logTwoBall

theorem center_sq0136 : (center0136.re : ℝ)^2 +
    (center0136.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0136]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0136 : work0136.theta.ok = true ∧
    work0136.jac.invOK = true ∧ acceptsUnitSq work0136.out = true := by
  norm_num [work0136, contact0136, tau0136, center0136, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0136 : CellCertificate where
  tauBall := tau0136
  contactCenter := center0136
  contactBall := contact0136
  work := work0136
  center_sq := center_sq0136
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0136.1
  jac_ok := checks0136.2.1
  accepted := checks0136.2.2

def tau0137 : RatBall :=
  ⟨⟨1/16, -17/80⟩, 3/160⟩
def center0137 : GaussianRat :=
  ⟨22688687/500000000, -149010417/1000000000⟩
def contact0137 : RatBall := localContactBall tau0137 center0137
def work0137 : RoundedTauEval :=
  evalTau precision tau0137 contact0137 logTwoBall

theorem center_sq0137 : (center0137.re : ℝ)^2 +
    (center0137.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0137]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0137 : work0137.theta.ok = true ∧
    work0137.jac.invOK = true ∧ acceptsUnitSq work0137.out = true := by
  norm_num [work0137, contact0137, tau0137, center0137, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0137 : CellCertificate where
  tauBall := tau0137
  contactCenter := center0137
  contactBall := contact0137
  work := work0137
  center_sq := center_sq0137
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0137.1
  jac_ok := checks0137.2.1
  accepted := checks0137.2.2

def tau0138 : RatBall :=
  ⟨⟨7/80, -17/80⟩, 3/160⟩
def center0138 : GaussianRat :=
  ⟨31712973/500000000, -37096923/250000000⟩
def contact0138 : RatBall := localContactBall tau0138 center0138
def work0138 : RoundedTauEval :=
  evalTau precision tau0138 contact0138 logTwoBall

theorem center_sq0138 : (center0138.re : ℝ)^2 +
    (center0138.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0138]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0138 : work0138.theta.ok = true ∧
    work0138.jac.invOK = true ∧ acceptsUnitSq work0138.out = true := by
  norm_num [work0138, contact0138, tau0138, center0138, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0138 : CellCertificate where
  tauBall := tau0138
  contactCenter := center0138
  contactBall := contact0138
  work := work0138
  center_sq := center_sq0138
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0138.1
  jac_ok := checks0138.2.1
  accepted := checks0138.2.2

def tau0139 : RatBall :=
  ⟨⟨9/80, -19/80⟩, 3/160⟩
def center0139 : GaussianRat :=
  ⟨20589547/250000000, -33110861/200000000⟩
def contact0139 : RatBall := localContactBall tau0139 center0139
def work0139 : RoundedTauEval :=
  evalTau precision tau0139 contact0139 logTwoBall

theorem center_sq0139 : (center0139.re : ℝ)^2 +
    (center0139.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0139]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0139 : work0139.theta.ok = true ∧
    work0139.jac.invOK = true ∧ acceptsUnitSq work0139.out = true := by
  norm_num [work0139, contact0139, tau0139, center0139, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0139 : CellCertificate where
  tauBall := tau0139
  contactCenter := center0139
  contactBall := contact0139
  work := work0139
  center_sq := center_sq0139
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0139.1
  jac_ok := checks0139.2.1
  accepted := checks0139.2.2

def tau0140 : RatBall :=
  ⟨⟨11/80, -19/80⟩, 3/160⟩
def center0140 : GaussianRat :=
  ⟨25094739/250000000, -82197279/500000000⟩
def contact0140 : RatBall := localContactBall tau0140 center0140
def work0140 : RoundedTauEval :=
  evalTau precision tau0140 contact0140 logTwoBall

theorem center_sq0140 : (center0140.re : ℝ)^2 +
    (center0140.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0140]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0140 : work0140.theta.ok = true ∧
    work0140.jac.invOK = true ∧ acceptsUnitSq work0140.out = true := by
  norm_num [work0140, contact0140, tau0140, center0140, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0140 : CellCertificate where
  tauBall := tau0140
  contactCenter := center0140
  contactBall := contact0140
  work := work0140
  center_sq := center_sq0140
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0140.1
  jac_ok := checks0140.2.1
  accepted := checks0140.2.2

def tau0141 : RatBall :=
  ⟨⟨9/80, -17/80⟩, 3/160⟩
def center0141 : GaussianRat :=
  ⟨4068673/50000000, -73782899/500000000⟩
def contact0141 : RatBall := localContactBall tau0141 center0141
def work0141 : RoundedTauEval :=
  evalTau precision tau0141 contact0141 logTwoBall

theorem center_sq0141 : (center0141.re : ℝ)^2 +
    (center0141.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0141]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0141 : work0141.theta.ok = true ∧
    work0141.jac.invOK = true ∧ acceptsUnitSq work0141.out = true := by
  norm_num [work0141, contact0141, tau0141, center0141, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0141 : CellCertificate where
  tauBall := tau0141
  contactCenter := center0141
  contactBall := contact0141
  work := work0141
  center_sq := center_sq0141
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0141.1
  jac_ok := checks0141.2.1
  accepted := checks0141.2.2

def tau0142 : RatBall :=
  ⟨⟨11/80, -17/80⟩, 3/160⟩
def center0142 : GaussianRat :=
  ⟨24798221/250000000, -36637923/250000000⟩
def contact0142 : RatBall := localContactBall tau0142 center0142
def work0142 : RoundedTauEval :=
  evalTau precision tau0142 contact0142 logTwoBall

theorem center_sq0142 : (center0142.re : ℝ)^2 +
    (center0142.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0142]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0142 : work0142.theta.ok = true ∧
    work0142.jac.invOK = true ∧ acceptsUnitSq work0142.out = true := by
  norm_num [work0142, contact0142, tau0142, center0142, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0142 : CellCertificate where
  tauBall := tau0142
  contactCenter := center0142
  contactBall := contact0142
  work := work0142
  center_sq := center_sq0142
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0142.1
  jac_ok := checks0142.2.1
  accepted := checks0142.2.2

def tau0143 : RatBall :=
  ⟨⟨13/80, -17/80⟩, 3/160⟩
def center0143 : GaussianRat :=
  ⟨58429249/500000000, -145353777/1000000000⟩
def contact0143 : RatBall := localContactBall tau0143 center0143
def work0143 : RoundedTauEval :=
  evalTau precision tau0143 contact0143 logTwoBall

theorem center_sq0143 : (center0143.re : ℝ)^2 +
    (center0143.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0143]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0143 : work0143.theta.ok = true ∧
    work0143.jac.invOK = true ∧ acceptsUnitSq work0143.out = true := by
  norm_num [work0143, contact0143, tau0143, center0143, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0143 : CellCertificate where
  tauBall := tau0143
  contactCenter := center0143
  contactBall := contact0143
  work := work0143
  center_sq := center_sq0143
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0143.1
  jac_ok := checks0143.2.1
  accepted := checks0143.2.2

def cells : List CellCertificate := [cell0136, cell0137, cell0138, cell0139, cell0140, cell0141, cell0142, cell0143]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0017
