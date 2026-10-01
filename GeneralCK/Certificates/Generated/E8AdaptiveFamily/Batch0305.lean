import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2440 : RatBall :=
  ⟨⟨73/320, 93/320⟩, 3/640⟩
def center2440 : GaussianRat :=
  ⟨84433841/500000000, 195452163/1000000000⟩
def contact2440 : RatBall := localContactBall tau2440 center2440
def work2440 : RoundedTauEval :=
  evalTau precision tau2440 contact2440 logTwoBall

theorem center_sq2440 : (center2440.re : ℝ)^2 +
    (center2440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2440 : work2440.theta.ok = true ∧
    work2440.jac.invOK = true ∧ acceptsUnitSq work2440.out = true := by
  norm_num [work2440, contact2440, tau2440, center2440, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2440 : CellCertificate where
  tauBall := tau2440
  contactCenter := center2440
  contactBall := contact2440
  work := work2440
  center_sq := center_sq2440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2440.1
  jac_ok := checks2440.2.1
  accepted := checks2440.2.2

def tau2441 : RatBall :=
  ⟨⟨15/64, 93/320⟩, 3/640⟩
def center2441 : GaussianRat :=
  ⟨173254189/1000000000, 38963859/200000000⟩
def contact2441 : RatBall := localContactBall tau2441 center2441
def work2441 : RoundedTauEval :=
  evalTau precision tau2441 contact2441 logTwoBall

theorem center_sq2441 : (center2441.re : ℝ)^2 +
    (center2441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2441 : work2441.theta.ok = true ∧
    work2441.jac.invOK = true ∧ acceptsUnitSq work2441.out = true := by
  norm_num [work2441, contact2441, tau2441, center2441, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2441 : CellCertificate where
  tauBall := tau2441
  contactCenter := center2441
  contactBall := contact2441
  work := work2441
  center_sq := center_sq2441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2441.1
  jac_ok := checks2441.2.1
  accepted := checks2441.2.2

def tau2442 : RatBall :=
  ⟨⟨73/320, 19/64⟩, 3/640⟩
def center2442 : GaussianRat :=
  ⟨16950309/100000000, 199854009/1000000000⟩
def contact2442 : RatBall := localContactBall tau2442 center2442
def work2442 : RoundedTauEval :=
  evalTau precision tau2442 contact2442 logTwoBall

theorem center_sq2442 : (center2442.re : ℝ)^2 +
    (center2442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2442 : work2442.theta.ok = true ∧
    work2442.jac.invOK = true ∧ acceptsUnitSq work2442.out = true := by
  norm_num [work2442, contact2442, tau2442, center2442, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2442 : CellCertificate where
  tauBall := tau2442
  contactCenter := center2442
  contactBall := contact2442
  work := work2442
  center_sq := center_sq2442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2442.1
  jac_ok := checks2442.2.1
  accepted := checks2442.2.2

def tau2443 : RatBall :=
  ⟨⟨15/64, 19/64⟩, 3/640⟩
def center2443 : GaussianRat :=
  ⟨43475599/250000000, 199203157/1000000000⟩
def contact2443 : RatBall := localContactBall tau2443 center2443
def work2443 : RoundedTauEval :=
  evalTau precision tau2443 contact2443 logTwoBall

theorem center_sq2443 : (center2443.re : ℝ)^2 +
    (center2443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2443 : work2443.theta.ok = true ∧
    work2443.jac.invOK = true ∧ acceptsUnitSq work2443.out = true := by
  norm_num [work2443, contact2443, tau2443, center2443, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2443 : CellCertificate where
  tauBall := tau2443
  contactCenter := center2443
  contactBall := contact2443
  work := work2443
  center_sq := center_sq2443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2443.1
  jac_ok := checks2443.2.1
  accepted := checks2443.2.2

def tau2444 : RatBall :=
  ⟨⟨77/320, 93/320⟩, 3/640⟩
def center2444 : GaussianRat :=
  ⟨44405679/250000000, 194173939/1000000000⟩
def contact2444 : RatBall := localContactBall tau2444 center2444
def work2444 : RoundedTauEval :=
  evalTau precision tau2444 contact2444 logTwoBall

theorem center_sq2444 : (center2444.re : ℝ)^2 +
    (center2444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2444 : work2444.theta.ok = true ∧
    work2444.jac.invOK = true ∧ acceptsUnitSq work2444.out = true := by
  norm_num [work2444, contact2444, tau2444, center2444, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2444 : CellCertificate where
  tauBall := tau2444
  contactCenter := center2444
  contactBall := contact2444
  work := work2444
  center_sq := center_sq2444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2444.1
  jac_ok := checks2444.2.1
  accepted := checks2444.2.2

def tau2445 : RatBall :=
  ⟨⟨79/320, 93/320⟩, 3/640⟩
def center2445 : GaussianRat :=
  ⟨90986481/500000000, 24189551/125000000⟩
def contact2445 : RatBall := localContactBall tau2445 center2445
def work2445 : RoundedTauEval :=
  evalTau precision tau2445 contact2445 logTwoBall

theorem center_sq2445 : (center2445.re : ℝ)^2 +
    (center2445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2445 : work2445.theta.ok = true ∧
    work2445.jac.invOK = true ∧ acceptsUnitSq work2445.out = true := by
  norm_num [work2445, contact2445, tau2445, center2445, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2445 : CellCertificate where
  tauBall := tau2445
  contactCenter := center2445
  contactBall := contact2445
  work := work2445
  center_sq := center_sq2445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2445.1
  jac_ok := checks2445.2.1
  accepted := checks2445.2.2

def tau2446 : RatBall :=
  ⟨⟨77/320, 19/64⟩, 3/640⟩
def center2446 : GaussianRat :=
  ⟨35656681/200000000, 198539511/1000000000⟩
def contact2446 : RatBall := localContactBall tau2446 center2446
def work2446 : RoundedTauEval :=
  evalTau precision tau2446 contact2446 logTwoBall

theorem center_sq2446 : (center2446.re : ℝ)^2 +
    (center2446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2446 : work2446.theta.ok = true ∧
    work2446.jac.invOK = true ∧ acceptsUnitSq work2446.out = true := by
  norm_num [work2446, contact2446, tau2446, center2446, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2446 : CellCertificate where
  tauBall := tau2446
  contactCenter := center2446
  contactBall := contact2446
  work := work2446
  center_sq := center_sq2446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2446.1
  jac_ok := checks2446.2.1
  accepted := checks2446.2.2

def tau2447 : RatBall :=
  ⟨⟨79/320, 19/64⟩, 3/640⟩
def center2447 : GaussianRat :=
  ⟨91322907/500000000, 98931697/500000000⟩
def contact2447 : RatBall := localContactBall tau2447 center2447
def work2447 : RoundedTauEval :=
  evalTau precision tau2447 contact2447 logTwoBall

theorem center_sq2447 : (center2447.re : ℝ)^2 +
    (center2447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2447 : work2447.theta.ok = true ∧
    work2447.jac.invOK = true ∧ acceptsUnitSq work2447.out = true := by
  norm_num [work2447, contact2447, tau2447, center2447, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2447 : CellCertificate where
  tauBall := tau2447
  contactCenter := center2447
  contactBall := contact2447
  work := work2447
  center_sq := center_sq2447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2447.1
  jac_ok := checks2447.2.1
  accepted := checks2447.2.2

def cells : List CellCertificate := [cell2440, cell2441, cell2442, cell2443, cell2444, cell2445, cell2446, cell2447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305
