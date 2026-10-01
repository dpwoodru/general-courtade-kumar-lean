import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0944 : RatBall :=
  ⟨⟨-11/160, 47/160⟩, 3/320⟩
def center0944 : GaussianRat :=
  ⟨-13053307/250000000, 208849073/1000000000⟩
def contact0944 : RatBall := localContactBall tau0944 center0944
def work0944 : RoundedTauEval :=
  evalTau precision tau0944 contact0944 logTwoBall

theorem center_sq0944 : (center0944.re : ℝ)^2 +
    (center0944.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0944]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0944 : work0944.theta.ok = true ∧
    work0944.jac.invOK = true ∧ acceptsUnitSq work0944.out = true := by
  norm_num [work0944, contact0944, tau0944, center0944, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0944 : CellCertificate where
  tauBall := tau0944
  contactCenter := center0944
  contactBall := contact0944
  work := work0944
  center_sq := center_sq0944
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0944.1
  jac_ok := checks0944.2.1
  accepted := checks0944.2.2

def tau0945 : RatBall :=
  ⟨⟨-9/160, 47/160⟩, 3/320⟩
def center0945 : GaussianRat :=
  ⟨-42754839/1000000000, 41848559/200000000⟩
def contact0945 : RatBall := localContactBall tau0945 center0945
def work0945 : RoundedTauEval :=
  evalTau precision tau0945 contact0945 logTwoBall

theorem center_sq0945 : (center0945.re : ℝ)^2 +
    (center0945.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0945]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0945 : work0945.theta.ok = true ∧
    work0945.jac.invOK = true ∧ acceptsUnitSq work0945.out = true := by
  norm_num [work0945, contact0945, tau0945, center0945, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0945 : CellCertificate where
  tauBall := tau0945
  contactCenter := center0945
  contactBall := contact0945
  work := work0945
  center_sq := center_sq0945
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0945.1
  jac_ok := checks0945.2.1
  accepted := checks0945.2.2

def tau0946 : RatBall :=
  ⟨⟨-27/160, 49/160⟩, 3/320⟩
def center0946 : GaussianRat :=
  ⟨-3988651/31250000, 53050431/250000000⟩
def contact0946 : RatBall := localContactBall tau0946 center0946
def work0946 : RoundedTauEval :=
  evalTau precision tau0946 contact0946 logTwoBall

theorem center_sq0946 : (center0946.re : ℝ)^2 +
    (center0946.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0946]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0946 : work0946.theta.ok = true ∧
    work0946.jac.invOK = true ∧ acceptsUnitSq work0946.out = true := by
  norm_num [work0946, contact0946, tau0946, center0946, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0946 : CellCertificate where
  tauBall := tau0946
  contactCenter := center0946
  contactBall := contact0946
  work := work0946
  center_sq := center_sq0946
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0946.1
  jac_ok := checks0946.2.1
  accepted := checks0946.2.2

def tau0947 : RatBall :=
  ⟨⟨-5/32, 49/160⟩, 3/320⟩
def center0947 : GaussianRat :=
  ⟨-23686489/200000000, 53305887/250000000⟩
def contact0947 : RatBall := localContactBall tau0947 center0947
def work0947 : RoundedTauEval :=
  evalTau precision tau0947 contact0947 logTwoBall

theorem center_sq0947 : (center0947.re : ℝ)^2 +
    (center0947.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0947]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0947 : work0947.theta.ok = true ∧
    work0947.jac.invOK = true ∧ acceptsUnitSq work0947.out = true := by
  norm_num [work0947, contact0947, tau0947, center0947, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0947 : CellCertificate where
  tauBall := tau0947
  contactCenter := center0947
  contactBall := contact0947
  work := work0947
  center_sq := center_sq0947
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0947.1
  jac_ok := checks0947.2.1
  accepted := checks0947.2.2

def tau0948 : RatBall :=
  ⟨⟨-23/160, 49/160⟩, 3/320⟩
def center0948 : GaussianRat :=
  ⟨-109172181/1000000000, 42835301/200000000⟩
def contact0948 : RatBall := localContactBall tau0948 center0948
def work0948 : RoundedTauEval :=
  evalTau precision tau0948 contact0948 logTwoBall

theorem center_sq0948 : (center0948.re : ℝ)^2 +
    (center0948.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0948]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0948 : work0948.theta.ok = true ∧
    work0948.jac.invOK = true ∧ acceptsUnitSq work0948.out = true := by
  norm_num [work0948, contact0948, tau0948, center0948, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0948 : CellCertificate where
  tauBall := tau0948
  contactCenter := center0948
  contactBall := contact0948
  work := work0948
  center_sq := center_sq0948
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0948.1
  jac_ok := checks0948.2.1
  accepted := checks0948.2.2

def tau0949 : RatBall :=
  ⟨⟨-21/160, 49/160⟩, 3/320⟩
def center0949 : GaussianRat :=
  ⟨-9985979/100000000, 43011679/200000000⟩
def contact0949 : RatBall := localContactBall tau0949 center0949
def work0949 : RoundedTauEval :=
  evalTau precision tau0949 contact0949 logTwoBall

theorem center_sq0949 : (center0949.re : ℝ)^2 +
    (center0949.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0949]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0949 : work0949.theta.ok = true ∧
    work0949.jac.invOK = true ∧ acceptsUnitSq work0949.out = true := by
  norm_num [work0949, contact0949, tau0949, center0949, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0949 : CellCertificate where
  tauBall := tau0949
  contactCenter := center0949
  contactBall := contact0949
  work := work0949
  center_sq := center_sq0949
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0949.1
  jac_ok := checks0949.2.1
  accepted := checks0949.2.2

def tau0950 : RatBall :=
  ⟨⟨-21/160, 51/160⟩, 3/320⟩
def center0950 : GaussianRat :=
  ⟨-100729897/1000000000, 44886561/200000000⟩
def contact0950 : RatBall := localContactBall tau0950 center0950
def work0950 : RoundedTauEval :=
  evalTau precision tau0950 contact0950 logTwoBall

theorem center_sq0950 : (center0950.re : ℝ)^2 +
    (center0950.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0950]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0950 : work0950.theta.ok = true ∧
    work0950.jac.invOK = true ∧ acceptsUnitSq work0950.out = true := by
  norm_num [work0950, contact0950, tau0950, center0950, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0950 : CellCertificate where
  tauBall := tau0950
  contactCenter := center0950
  contactBall := contact0950
  work := work0950
  center_sq := center_sq0950
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0950.1
  jac_ok := checks0950.2.1
  accepted := checks0950.2.2

def tau0951 : RatBall :=
  ⟨⟨-19/160, 49/160⟩, 3/320⟩
def center0951 : GaussianRat :=
  ⟨-90499187/1000000000, 215867147/1000000000⟩
def contact0951 : RatBall := localContactBall tau0951 center0951
def work0951 : RoundedTauEval :=
  evalTau precision tau0951 contact0951 logTwoBall

theorem center_sq0951 : (center0951.re : ℝ)^2 +
    (center0951.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0951]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0951 : work0951.theta.ok = true ∧
    work0951.jac.invOK = true ∧ acceptsUnitSq work0951.out = true := by
  norm_num [work0951, contact0951, tau0951, center0951, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0951 : CellCertificate where
  tauBall := tau0951
  contactCenter := center0951
  contactBall := contact0951
  work := work0951
  center_sq := center_sq0951
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0951.1
  jac_ok := checks0951.2.1
  accepted := checks0951.2.2

def cells : List CellCertificate := [cell0944, cell0945, cell0946, cell0947, cell0948, cell0949, cell0950, cell0951]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118
