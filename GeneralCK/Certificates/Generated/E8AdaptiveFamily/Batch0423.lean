import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3384 : RatBall :=
  ⟨⟨-49/640, 243/640⟩, 3/1280⟩
def center3384 : GaussianRat :=
  ⟨-12430013/200000000, 275443499/1000000000⟩
def contact3384 : RatBall := localContactBall tau3384 center3384
def work3384 : RoundedTauEval :=
  evalTau precision tau3384 contact3384 logTwoBall

theorem center_sq3384 : (center3384.re : ℝ)^2 +
    (center3384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3384 : work3384.theta.ok = true ∧
    work3384.jac.invOK = true ∧ acceptsUnitSq work3384.out = true := by
  norm_num [work3384, contact3384, tau3384, center3384, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3384 : CellCertificate where
  tauBall := tau3384
  contactCenter := center3384
  contactBall := contact3384
  work := work3384
  center_sq := center_sq3384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3384.1
  jac_ok := checks3384.2.1
  accepted := checks3384.2.2

def tau3385 : RatBall :=
  ⟨⟨-11/128, 49/128⟩, 3/1280⟩
def center3385 : GaussianRat :=
  ⟨-69887307/1000000000, 277394317/1000000000⟩
def contact3385 : RatBall := localContactBall tau3385 center3385
def work3385 : RoundedTauEval :=
  evalTau precision tau3385 contact3385 logTwoBall

theorem center_sq3385 : (center3385.re : ℝ)^2 +
    (center3385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3385 : work3385.theta.ok = true ∧
    work3385.jac.invOK = true ∧ acceptsUnitSq work3385.out = true := by
  norm_num [work3385, contact3385, tau3385, center3385, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3385 : CellCertificate where
  tauBall := tau3385
  contactCenter := center3385
  contactBall := contact3385
  work := work3385
  center_sq := center_sq3385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3385.1
  jac_ok := checks3385.2.1
  accepted := checks3385.2.2

def tau3386 : RatBall :=
  ⟨⟨-53/640, 49/128⟩, 3/1280⟩
def center3386 : GaussianRat :=
  ⟨-4210637/62500000, 55518211/200000000⟩
def contact3386 : RatBall := localContactBall tau3386 center3386
def work3386 : RoundedTauEval :=
  evalTau precision tau3386 contact3386 logTwoBall

theorem center_sq3386 : (center3386.re : ℝ)^2 +
    (center3386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3386 : work3386.theta.ok = true ∧
    work3386.jac.invOK = true ∧ acceptsUnitSq work3386.out = true := by
  norm_num [work3386, contact3386, tau3386, center3386, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3386 : CellCertificate where
  tauBall := tau3386
  contactCenter := center3386
  contactBall := contact3386
  work := work3386
  center_sq := center_sq3386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3386.1
  jac_ok := checks3386.2.1
  accepted := checks3386.2.2

def tau3387 : RatBall :=
  ⟨⟨-11/128, 247/640⟩, 3/1280⟩
def center3387 : GaussianRat :=
  ⟨-70088901/1000000000, 139956777/500000000⟩
def contact3387 : RatBall := localContactBall tau3387 center3387
def work3387 : RoundedTauEval :=
  evalTau precision tau3387 contact3387 logTwoBall

theorem center_sq3387 : (center3387.re : ℝ)^2 +
    (center3387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3387 : work3387.theta.ok = true ∧
    work3387.jac.invOK = true ∧ acceptsUnitSq work3387.out = true := by
  norm_num [work3387, contact3387, tau3387, center3387, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3387 : CellCertificate where
  tauBall := tau3387
  contactCenter := center3387
  contactBall := contact3387
  work := work3387
  center_sq := center_sq3387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3387.1
  jac_ok := checks3387.2.1
  accepted := checks3387.2.2

def tau3388 : RatBall :=
  ⟨⟨-53/640, 247/640⟩, 3/1280⟩
def center3388 : GaussianRat :=
  ⟨-33782393/500000000, 56022603/200000000⟩
def contact3388 : RatBall := localContactBall tau3388 center3388
def work3388 : RoundedTauEval :=
  evalTau precision tau3388 contact3388 logTwoBall

theorem center_sq3388 : (center3388.re : ℝ)^2 +
    (center3388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3388 : work3388.theta.ok = true ∧
    work3388.jac.invOK = true ∧ acceptsUnitSq work3388.out = true := by
  norm_num [work3388, contact3388, tau3388, center3388, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3388 : CellCertificate where
  tauBall := tau3388
  contactCenter := center3388
  contactBall := contact3388
  work := work3388
  center_sq := center_sq3388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3388.1
  jac_ok := checks3388.2.1
  accepted := checks3388.2.2

def tau3389 : RatBall :=
  ⟨⟨-51/640, 49/128⟩, 3/1280⟩
def center3389 : GaussianRat :=
  ⟨-3242521/50000000, 138890411/500000000⟩
def contact3389 : RatBall := localContactBall tau3389 center3389
def work3389 : RoundedTauEval :=
  evalTau precision tau3389 contact3389 logTwoBall

theorem center_sq3389 : (center3389.re : ℝ)^2 +
    (center3389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3389 : work3389.theta.ok = true ∧
    work3389.jac.invOK = true ∧ acceptsUnitSq work3389.out = true := by
  norm_num [work3389, contact3389, tau3389, center3389, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3389 : CellCertificate where
  tauBall := tau3389
  contactCenter := center3389
  contactBall := contact3389
  work := work3389
  center_sq := center_sq3389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3389.1
  jac_ok := checks3389.2.1
  accepted := checks3389.2.2

def tau3390 : RatBall :=
  ⟨⟨-49/640, 49/128⟩, 3/1280⟩
def center3390 : GaussianRat :=
  ⟨-31164041/500000000, 277963583/1000000000⟩
def contact3390 : RatBall := localContactBall tau3390 center3390
def work3390 : RoundedTauEval :=
  evalTau precision tau3390 contact3390 logTwoBall

theorem center_sq3390 : (center3390.re : ℝ)^2 +
    (center3390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3390 : work3390.theta.ok = true ∧
    work3390.jac.invOK = true ∧ acceptsUnitSq work3390.out = true := by
  norm_num [work3390, contact3390, tau3390, center3390, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3390 : CellCertificate where
  tauBall := tau3390
  contactCenter := center3390
  contactBall := contact3390
  work := work3390
  center_sq := center_sq3390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3390.1
  jac_ok := checks3390.2.1
  accepted := checks3390.2.2

def tau3391 : RatBall :=
  ⟨⟨-51/640, 247/640⟩, 3/1280⟩
def center3391 : GaussianRat :=
  ⟨-32518989/500000000, 70076353/250000000⟩
def contact3391 : RatBall := localContactBall tau3391 center3391
def work3391 : RoundedTauEval :=
  evalTau precision tau3391 contact3391 logTwoBall

theorem center_sq3391 : (center3391.re : ℝ)^2 +
    (center3391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3391 : work3391.theta.ok = true ∧
    work3391.jac.invOK = true ∧ acceptsUnitSq work3391.out = true := by
  norm_num [work3391, contact3391, tau3391, center3391, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3391 : CellCertificate where
  tauBall := tau3391
  contactCenter := center3391
  contactBall := contact3391
  work := work3391
  center_sq := center_sq3391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3391.1
  jac_ok := checks3391.2.1
  accepted := checks3391.2.2

def cells : List CellCertificate := [cell3384, cell3385, cell3386, cell3387, cell3388, cell3389, cell3390, cell3391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423
