import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0166

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1328 : RatBall :=
  ⟨⟨-15/64, -91/320⟩, 3/640⟩
def center1328 : GaussianRat :=
  ⟨-34524793/200000000, -2380599/12500000⟩
def contact1328 : RatBall := localContactBall tau1328 center1328
def work1328 : RoundedTauEval :=
  evalTau precision tau1328 contact1328 logTwoBall

theorem center_sq1328 : (center1328.re : ℝ)^2 +
    (center1328.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1328]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1328 : work1328.theta.ok = true ∧
    work1328.jac.invOK = true ∧ acceptsUnitSq work1328.out = true := by
  norm_num [work1328, contact1328, tau1328, center1328, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1328 : CellCertificate where
  tauBall := tau1328
  contactCenter := center1328
  contactBall := contact1328
  work := work1328
  center_sq := center_sq1328
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1328.1
  jac_ok := checks1328.2.1
  accepted := checks1328.2.2

def tau1329 : RatBall :=
  ⟨⟨-73/320, -91/320⟩, 3/640⟩
def center1329 : GaussianRat :=
  ⟨-33649989/200000000, -38212623/200000000⟩
def contact1329 : RatBall := localContactBall tau1329 center1329
def work1329 : RoundedTauEval :=
  evalTau precision tau1329 contact1329 logTwoBall

theorem center_sq1329 : (center1329.re : ℝ)^2 +
    (center1329.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1329]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1329 : work1329.theta.ok = true ∧
    work1329.jac.invOK = true ∧ acceptsUnitSq work1329.out = true := by
  norm_num [work1329, contact1329, tau1329, center1329, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1329 : CellCertificate where
  tauBall := tau1329
  contactCenter := center1329
  contactBall := contact1329
  work := work1329
  center_sq := center_sq1329
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1329.1
  jac_ok := checks1329.2.1
  accepted := checks1329.2.2

def tau1330 : RatBall :=
  ⟨⟨-15/64, -89/320⟩, 3/640⟩
def center1330 : GaussianRat :=
  ⟨-21501427/125000000, -186088727/1000000000⟩
def contact1330 : RatBall := localContactBall tau1330 center1330
def work1330 : RoundedTauEval :=
  evalTau precision tau1330 contact1330 logTwoBall

theorem center_sq1330 : (center1330.re : ℝ)^2 +
    (center1330.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1330]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1330 : work1330.theta.ok = true ∧
    work1330.jac.invOK = true ∧ acceptsUnitSq work1330.out = true := by
  norm_num [work1330, contact1330, tau1330, center1330, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1330 : CellCertificate where
  tauBall := tau1330
  contactCenter := center1330
  contactBall := contact1330
  work := work1330
  center_sq := center_sq1330
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1330.1
  jac_ok := checks1330.2.1
  accepted := checks1330.2.2

def tau1331 : RatBall :=
  ⟨⟨-73/320, -89/320⟩, 3/640⟩
def center1331 : GaussianRat :=
  ⟨-6705983/40000000, -46671637/250000000⟩
def contact1331 : RatBall := localContactBall tau1331 center1331
def work1331 : RoundedTauEval :=
  evalTau precision tau1331 contact1331 logTwoBall

theorem center_sq1331 : (center1331.re : ℝ)^2 +
    (center1331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1331 : work1331.theta.ok = true ∧
    work1331.jac.invOK = true ∧ acceptsUnitSq work1331.out = true := by
  norm_num [work1331, contact1331, tau1331, center1331, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1331 : CellCertificate where
  tauBall := tau1331
  contactCenter := center1331
  contactBall := contact1331
  work := work1331
  center_sq := center_sq1331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1331.1
  jac_ok := checks1331.2.1
  accepted := checks1331.2.2

def tau1332 : RatBall :=
  ⟨⟨-71/320, -19/64⟩, 3/640⟩
def center1332 : GaussianRat :=
  ⟨-165085801/1000000000, -40098349/200000000⟩
def contact1332 : RatBall := localContactBall tau1332 center1332
def work1332 : RoundedTauEval :=
  evalTau precision tau1332 contact1332 logTwoBall

theorem center_sq1332 : (center1332.re : ℝ)^2 +
    (center1332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1332 : work1332.theta.ok = true ∧
    work1332.jac.invOK = true ∧ acceptsUnitSq work1332.out = true := by
  norm_num [work1332, contact1332, tau1332, center1332, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1332 : CellCertificate where
  tauBall := tau1332
  contactCenter := center1332
  contactBall := contact1332
  work := work1332
  center_sq := center_sq1332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1332.1
  jac_ok := checks1332.2.1
  accepted := checks1332.2.2

def tau1333 : RatBall :=
  ⟨⟨-69/320, -19/64⟩, 3/640⟩
def center1333 : GaussianRat :=
  ⟨-80325427/500000000, -201116047/1000000000⟩
def contact1333 : RatBall := localContactBall tau1333 center1333
def work1333 : RoundedTauEval :=
  evalTau precision tau1333 contact1333 logTwoBall

theorem center_sq1333 : (center1333.re : ℝ)^2 +
    (center1333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1333 : work1333.theta.ok = true ∧
    work1333.jac.invOK = true ∧ acceptsUnitSq work1333.out = true := by
  norm_num [work1333, contact1333, tau1333, center1333, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1333 : CellCertificate where
  tauBall := tau1333
  contactCenter := center1333
  contactBall := contact1333
  work := work1333
  center_sq := center_sq1333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1333.1
  jac_ok := checks1333.2.1
  accepted := checks1333.2.2

def tau1334 : RatBall :=
  ⟨⟨-71/320, -93/320⟩, 3/640⟩
def center1334 : GaussianRat :=
  ⟨-82231753/500000000, -98036117/500000000⟩
def contact1334 : RatBall := localContactBall tau1334 center1334
def work1334 : RoundedTauEval :=
  evalTau precision tau1334 contact1334 logTwoBall

theorem center_sq1334 : (center1334.re : ℝ)^2 +
    (center1334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1334 : work1334.theta.ok = true ∧
    work1334.jac.invOK = true ∧ acceptsUnitSq work1334.out = true := by
  norm_num [work1334, contact1334, tau1334, center1334, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1334 : CellCertificate where
  tauBall := tau1334
  contactCenter := center1334
  contactBall := contact1334
  work := work1334
  center_sq := center_sq1334
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1334.1
  jac_ok := checks1334.2.1
  accepted := checks1334.2.2

def tau1335 : RatBall :=
  ⟨⟨-69/320, -93/320⟩, 3/640⟩
def center1335 : GaussianRat :=
  ⟨-32008397/200000000, -245849/1250000⟩
def contact1335 : RatBall := localContactBall tau1335 center1335
def work1335 : RoundedTauEval :=
  evalTau precision tau1335 contact1335 logTwoBall

theorem center_sq1335 : (center1335.re : ℝ)^2 +
    (center1335.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1335]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1335 : work1335.theta.ok = true ∧
    work1335.jac.invOK = true ∧ acceptsUnitSq work1335.out = true := by
  norm_num [work1335, contact1335, tau1335, center1335, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1335 : CellCertificate where
  tauBall := tau1335
  contactCenter := center1335
  contactBall := contact1335
  work := work1335
  center_sq := center_sq1335
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1335.1
  jac_ok := checks1335.2.1
  accepted := checks1335.2.2

def cells : List CellCertificate := [cell1328, cell1329, cell1330, cell1331, cell1332, cell1333, cell1334, cell1335]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0166
