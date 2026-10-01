import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0960 : RatBall :=
  ⟨⟨-11/160, 49/160⟩, 3/320⟩
def center0960 : GaussianRat :=
  ⟨-52658297/1000000000, 109167283/500000000⟩
def contact0960 : RatBall := localContactBall tau0960 center0960
def work0960 : RoundedTauEval :=
  evalTau precision tau0960 contact0960 logTwoBall

theorem center_sq0960 : (center0960.re : ℝ)^2 +
    (center0960.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0960]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0960 : work0960.theta.ok = true ∧
    work0960.jac.invOK = true ∧ acceptsUnitSq work0960.out = true := by
  norm_num [work0960, contact0960, tau0960, center0960, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0960 : CellCertificate where
  tauBall := tau0960
  contactCenter := center0960
  contactBall := contact0960
  work := work0960
  center_sq := center_sq0960
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0960.1
  jac_ok := checks0960.2.1
  accepted := checks0960.2.2

def tau0961 : RatBall :=
  ⟨⟨-9/160, 49/160⟩, 3/320⟩
def center0961 : GaussianRat :=
  ⟨-43120523/1000000000, 109375967/500000000⟩
def contact0961 : RatBall := localContactBall tau0961 center0961
def work0961 : RoundedTauEval :=
  evalTau precision tau0961 contact0961 logTwoBall

theorem center_sq0961 : (center0961.re : ℝ)^2 +
    (center0961.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0961]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0961 : work0961.theta.ok = true ∧
    work0961.jac.invOK = true ∧ acceptsUnitSq work0961.out = true := by
  norm_num [work0961, contact0961, tau0961, center0961, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0961 : CellCertificate where
  tauBall := tau0961
  contactCenter := center0961
  contactBall := contact0961
  work := work0961
  center_sq := center_sq0961
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0961.1
  jac_ok := checks0961.2.1
  accepted := checks0961.2.2

def tau0962 : RatBall :=
  ⟨⟨-11/160, 51/160⟩, 3/320⟩
def center0962 : GaussianRat :=
  ⟨-53129867/1000000000, 56975307/250000000⟩
def contact0962 : RatBall := localContactBall tau0962 center0962
def work0962 : RoundedTauEval :=
  evalTau precision tau0962 contact0962 logTwoBall

theorem center_sq0962 : (center0962.re : ℝ)^2 +
    (center0962.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0962]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0962 : work0962.theta.ok = true ∧
    work0962.jac.invOK = true ∧ acceptsUnitSq work0962.out = true := by
  norm_num [work0962, contact0962, tau0962, center0962, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0962 : CellCertificate where
  tauBall := tau0962
  contactCenter := center0962
  contactBall := contact0962
  work := work0962
  center_sq := center_sq0962
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0962.1
  jac_ok := checks0962.2.1
  accepted := checks0962.2.2

def tau0963 : RatBall :=
  ⟨⟨-9/160, 51/160⟩, 3/320⟩
def center0963 : GaussianRat :=
  ⟨-21754011/500000000, 445983/1953125⟩
def contact0963 : RatBall := localContactBall tau0963 center0963
def work0963 : RoundedTauEval :=
  evalTau precision tau0963 contact0963 logTwoBall

theorem center_sq0963 : (center0963.re : ℝ)^2 +
    (center0963.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0963]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0963 : work0963.theta.ok = true ∧
    work0963.jac.invOK = true ∧ acceptsUnitSq work0963.out = true := by
  norm_num [work0963, contact0963, tau0963, center0963, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0963 : CellCertificate where
  tauBall := tau0963
  contactCenter := center0963
  contactBall := contact0963
  work := work0963
  center_sq := center_sq0963
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0963.1
  jac_ok := checks0963.2.1
  accepted := checks0963.2.2

def tau0964 : RatBall :=
  ⟨⟨-3/32, 53/160⟩, 3/320⟩
def center0964 : GaussianRat :=
  ⟨-72958787/1000000000, 47269393/200000000⟩
def contact0964 : RatBall := localContactBall tau0964 center0964
def work0964 : RoundedTauEval :=
  evalTau precision tau0964 contact0964 logTwoBall

theorem center_sq0964 : (center0964.re : ℝ)^2 +
    (center0964.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0964]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0964 : work0964.theta.ok = true ∧
    work0964.jac.invOK = true ∧ acceptsUnitSq work0964.out = true := by
  norm_num [work0964, contact0964, tau0964, center0964, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0964 : CellCertificate where
  tauBall := tau0964
  contactCenter := center0964
  contactBall := contact0964
  work := work0964
  center_sq := center_sq0964
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0964.1
  jac_ok := checks0964.2.1
  accepted := checks0964.2.2

def tau0965 : RatBall :=
  ⟨⟨-13/160, 53/160⟩, 3/320⟩
def center0965 : GaussianRat :=
  ⟨-63310961/1000000000, 236995059/1000000000⟩
def contact0965 : RatBall := localContactBall tau0965 center0965
def work0965 : RoundedTauEval :=
  evalTau precision tau0965 contact0965 logTwoBall

theorem center_sq0965 : (center0965.re : ℝ)^2 +
    (center0965.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0965]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0965 : work0965.theta.ok = true ∧
    work0965.jac.invOK = true ∧ acceptsUnitSq work0965.out = true := by
  norm_num [work0965, contact0965, tau0965, center0965, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0965 : CellCertificate where
  tauBall := tau0965
  contactCenter := center0965
  contactBall := contact0965
  work := work0965
  center_sq := center_sq0965
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0965.1
  jac_ok := checks0965.2.1
  accepted := checks0965.2.2

def tau0966 : RatBall :=
  ⟨⟨-11/160, 53/160⟩, 3/320⟩
def center0966 : GaussianRat :=
  ⟨-53629143/1000000000, 118776899/500000000⟩
def contact0966 : RatBall := localContactBall tau0966 center0966
def work0966 : RoundedTauEval :=
  evalTau precision tau0966 contact0966 logTwoBall

theorem center_sq0966 : (center0966.re : ℝ)^2 +
    (center0966.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0966]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0966 : work0966.theta.ok = true ∧
    work0966.jac.invOK = true ∧ acceptsUnitSq work0966.out = true := by
  norm_num [work0966, contact0966, tau0966, center0966, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0966 : CellCertificate where
  tauBall := tau0966
  contactCenter := center0966
  contactBall := contact0966
  work := work0966
  center_sq := center_sq0966
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0966.1
  jac_ok := checks0966.2.1
  accepted := checks0966.2.2

def tau0967 : RatBall :=
  ⟨⟨-9/160, 53/160⟩, 3/320⟩
def center0967 : GaussianRat :=
  ⟨-43918333/1000000000, 238021713/1000000000⟩
def contact0967 : RatBall := localContactBall tau0967 center0967
def work0967 : RoundedTauEval :=
  evalTau precision tau0967 contact0967 logTwoBall

theorem center_sq0967 : (center0967.re : ℝ)^2 +
    (center0967.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0967]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0967 : work0967.theta.ok = true ∧
    work0967.jac.invOK = true ∧ acceptsUnitSq work0967.out = true := by
  norm_num [work0967, contact0967, tau0967, center0967, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0967 : CellCertificate where
  tauBall := tau0967
  contactCenter := center0967
  contactBall := contact0967
  work := work0967
  center_sq := center_sq0967
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0967.1
  jac_ok := checks0967.2.1
  accepted := checks0967.2.2

def cells : List CellCertificate := [cell0960, cell0961, cell0962, cell0963, cell0964, cell0965, cell0966, cell0967]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120
