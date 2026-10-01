import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3304 : RatBall :=
  ⟨⟨-17/128, 237/640⟩, 3/1280⟩
def center3304 : GaussianRat :=
  ⟨-106097509/1000000000, 131912477/500000000⟩
def contact3304 : RatBall := localContactBall tau3304 center3304
def work3304 : RoundedTauEval :=
  evalTau precision tau3304 contact3304 logTwoBall

theorem center_sq3304 : (center3304.re : ℝ)^2 +
    (center3304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3304 : work3304.theta.ok = true ∧
    work3304.jac.invOK = true ∧ acceptsUnitSq work3304.out = true := by
  norm_num [work3304, contact3304, tau3304, center3304, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3304 : CellCertificate where
  tauBall := tau3304
  contactCenter := center3304
  contactBall := contact3304
  work := work3304
  center_sq := center_sq3304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3304.1
  jac_ok := checks3304.2.1
  accepted := checks3304.2.2

def tau3305 : RatBall :=
  ⟨⟨-87/640, 239/640⟩, 3/1280⟩
def center3305 : GaussianRat :=
  ⟨-4353093/40000000, 53195483/200000000⟩
def contact3305 : RatBall := localContactBall tau3305 center3305
def work3305 : RoundedTauEval :=
  evalTau precision tau3305 contact3305 logTwoBall

theorem center_sq3305 : (center3305.re : ℝ)^2 +
    (center3305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3305 : work3305.theta.ok = true ∧
    work3305.jac.invOK = true ∧ acceptsUnitSq work3305.out = true := by
  norm_num [work3305, contact3305, tau3305, center3305, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3305 : CellCertificate where
  tauBall := tau3305
  contactCenter := center3305
  contactBall := contact3305
  work := work3305
  center_sq := center_sq3305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3305.1
  jac_ok := checks3305.2.1
  accepted := checks3305.2.2

def tau3306 : RatBall :=
  ⟨⟨-17/128, 239/640⟩, 3/1280⟩
def center3306 : GaussianRat :=
  ⟨-10638319/100000000, 266268043/1000000000⟩
def contact3306 : RatBall := localContactBall tau3306 center3306
def work3306 : RoundedTauEval :=
  evalTau precision tau3306 contact3306 logTwoBall

theorem center_sq3306 : (center3306.re : ℝ)^2 +
    (center3306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3306 : work3306.theta.ok = true ∧
    work3306.jac.invOK = true ∧ acceptsUnitSq work3306.out = true := by
  norm_num [work3306, contact3306, tau3306, center3306, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3306 : CellCertificate where
  tauBall := tau3306
  contactCenter := center3306
  contactBall := contact3306
  work := work3306
  center_sq := center_sq3306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3306.1
  jac_ok := checks3306.2.1
  accepted := checks3306.2.2

def tau3307 : RatBall :=
  ⟨⟨-83/640, 237/640⟩, 3/1280⟩
def center3307 : GaussianRat :=
  ⟨-6478469/62500000, 132052859/500000000⟩
def contact3307 : RatBall := localContactBall tau3307 center3307
def work3307 : RoundedTauEval :=
  evalTau precision tau3307 contact3307 logTwoBall

theorem center_sq3307 : (center3307.re : ℝ)^2 +
    (center3307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3307 : work3307.theta.ok = true ∧
    work3307.jac.invOK = true ∧ acceptsUnitSq work3307.out = true := by
  norm_num [work3307, contact3307, tau3307, center3307, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3307 : CellCertificate where
  tauBall := tau3307
  contactCenter := center3307
  contactBall := contact3307
  work := work3307
  center_sq := center_sq3307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3307.1
  jac_ok := checks3307.2.1
  accepted := checks3307.2.2

def tau3308 : RatBall :=
  ⟨⟨-81/640, 237/640⟩, 3/1280⟩
def center3308 : GaussianRat :=
  ⟨-101209731/1000000000, 10575219/40000000⟩
def contact3308 : RatBall := localContactBall tau3308 center3308
def work3308 : RoundedTauEval :=
  evalTau precision tau3308 contact3308 logTwoBall

theorem center_sq3308 : (center3308.re : ℝ)^2 +
    (center3308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3308 : work3308.theta.ok = true ∧
    work3308.jac.invOK = true ∧ acceptsUnitSq work3308.out = true := by
  norm_num [work3308, contact3308, tau3308, center3308, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3308 : CellCertificate where
  tauBall := tau3308
  contactCenter := center3308
  contactBall := contact3308
  work := work3308
  center_sq := center_sq3308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3308.1
  jac_ok := checks3308.2.1
  accepted := checks3308.2.2

def tau3309 : RatBall :=
  ⟨⟨-83/640, 239/640⟩, 3/1280⟩
def center3309 : GaussianRat :=
  ⟨-103935163/1000000000, 66638159/250000000⟩
def contact3309 : RatBall := localContactBall tau3309 center3309
def work3309 : RoundedTauEval :=
  evalTau precision tau3309 contact3309 logTwoBall

theorem center_sq3309 : (center3309.re : ℝ)^2 +
    (center3309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3309 : work3309.theta.ok = true ∧
    work3309.jac.invOK = true ∧ acceptsUnitSq work3309.out = true := by
  norm_num [work3309, contact3309, tau3309, center3309, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3309 : CellCertificate where
  tauBall := tau3309
  contactCenter := center3309
  contactBall := contact3309
  work := work3309
  center_sq := center_sq3309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3309.1
  jac_ok := checks3309.2.1
  accepted := checks3309.2.2

def tau3310 : RatBall :=
  ⟨⟨-81/640, 239/640⟩, 3/1280⟩
def center3310 : GaussianRat :=
  ⟨-50741661/500000000, 53366229/200000000⟩
def contact3310 : RatBall := localContactBall tau3310 center3310
def work3310 : RoundedTauEval :=
  evalTau precision tau3310 contact3310 logTwoBall

theorem center_sq3310 : (center3310.re : ℝ)^2 +
    (center3310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3310 : work3310.theta.ok = true ∧
    work3310.jac.invOK = true ∧ acceptsUnitSq work3310.out = true := by
  norm_num [work3310, contact3310, tau3310, center3310, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3310 : CellCertificate where
  tauBall := tau3310
  contactCenter := center3310
  contactBall := contact3310
  work := work3310
  center_sq := center_sq3310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3310.1
  jac_ok := checks3310.2.1
  accepted := checks3310.2.2

def tau3311 : RatBall :=
  ⟨⟨-79/640, 237/640⟩, 3/1280⟩
def center3311 : GaussianRat :=
  ⟨-98760267/1000000000, 132324589/500000000⟩
def contact3311 : RatBall := localContactBall tau3311 center3311
def work3311 : RoundedTauEval :=
  evalTau precision tau3311 contact3311 logTwoBall

theorem center_sq3311 : (center3311.re : ℝ)^2 +
    (center3311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3311 : work3311.theta.ok = true ∧
    work3311.jac.invOK = true ∧ acceptsUnitSq work3311.out = true := by
  norm_num [work3311, contact3311, tau3311, center3311, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3311 : CellCertificate where
  tauBall := tau3311
  contactCenter := center3311
  contactBall := contact3311
  work := work3311
  center_sq := center_sq3311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3311.1
  jac_ok := checks3311.2.1
  accepted := checks3311.2.2

def cells : List CellCertificate := [cell3304, cell3305, cell3306, cell3307, cell3308, cell3309, cell3310, cell3311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413
