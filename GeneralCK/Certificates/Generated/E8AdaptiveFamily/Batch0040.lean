import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0320 : RatBall :=
  ⟨⟨19/80, 13/80⟩, 3/160⟩
def center0320 : GaussianRat :=
  ⟨41411389/250000000, 107116873/1000000000⟩
def contact0320 : RatBall := localContactBall tau0320 center0320
def work0320 : RoundedTauEval :=
  evalTau precision tau0320 contact0320 logTwoBall

theorem center_sq0320 : (center0320.re : ℝ)^2 +
    (center0320.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0320 : work0320.theta.ok = true ∧
    work0320.jac.invOK = true ∧ acceptsUnitSq work0320.out = true := by
  norm_num [work0320, contact0320, tau0320, center0320, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0320 : CellCertificate where
  tauBall := tau0320
  contactCenter := center0320
  contactBall := contact0320
  work := work0320
  center_sq := center_sq0320
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0320.1
  jac_ok := checks0320.2.1
  accepted := checks0320.2.2

def tau0321 : RatBall :=
  ⟨⟨17/80, 3/16⟩, 3/160⟩
def center0321 : GaussianRat :=
  ⟨150128589/1000000000, 25067823/200000000⟩
def contact0321 : RatBall := localContactBall tau0321 center0321
def work0321 : RoundedTauEval :=
  evalTau precision tau0321 contact0321 logTwoBall

theorem center_sq0321 : (center0321.re : ℝ)^2 +
    (center0321.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0321]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0321 : work0321.theta.ok = true ∧
    work0321.jac.invOK = true ∧ acceptsUnitSq work0321.out = true := by
  norm_num [work0321, contact0321, tau0321, center0321, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0321 : CellCertificate where
  tauBall := tau0321
  contactCenter := center0321
  contactBall := contact0321
  work := work0321
  center_sq := center_sq0321
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0321.1
  jac_ok := checks0321.2.1
  accepted := checks0321.2.2

def tau0322 : RatBall :=
  ⟨⟨21/80, 13/80⟩, 3/160⟩
def center0322 : GaussianRat :=
  ⟨4555953/25000000, 105764329/1000000000⟩
def contact0322 : RatBall := localContactBall tau0322 center0322
def work0322 : RoundedTauEval :=
  evalTau precision tau0322 contact0322 logTwoBall

theorem center_sq0322 : (center0322.re : ℝ)^2 +
    (center0322.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0322]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0322 : work0322.theta.ok = true ∧
    work0322.jac.invOK = true ∧ acceptsUnitSq work0322.out = true := by
  norm_num [work0322, contact0322, tau0322, center0322, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0322 : CellCertificate where
  tauBall := tau0322
  contactCenter := center0322
  contactBall := contact0322
  work := work0322
  center_sq := center_sq0322
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0322.1
  jac_ok := checks0322.2.1
  accepted := checks0322.2.2

def tau0323 : RatBall :=
  ⟨⟨5/16, 9/80⟩, 3/160⟩
def center0323 : GaussianRat :=
  ⟨106033397/500000000, 70959907/1000000000⟩
def contact0323 : RatBall := localContactBall tau0323 center0323
def work0323 : RoundedTauEval :=
  evalTau precision tau0323 contact0323 logTwoBall

theorem center_sq0323 : (center0323.re : ℝ)^2 +
    (center0323.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0323]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0323 : work0323.theta.ok = true ∧
    work0323.jac.invOK = true ∧ acceptsUnitSq work0323.out = true := by
  norm_num [work0323, contact0323, tau0323, center0323, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0323 : CellCertificate where
  tauBall := tau0323
  contactCenter := center0323
  contactBall := contact0323
  work := work0323
  center_sq := center_sq0323
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0323.1
  jac_ok := checks0323.2.1
  accepted := checks0323.2.2

def tau0324 : RatBall :=
  ⟨⟨1/80, 17/80⟩, 3/160⟩
def center0324 : GaussianRat :=
  ⟨2272549/250000000, 14963863/100000000⟩
def contact0324 : RatBall := localContactBall tau0324 center0324
def work0324 : RoundedTauEval :=
  evalTau precision tau0324 contact0324 logTwoBall

theorem center_sq0324 : (center0324.re : ℝ)^2 +
    (center0324.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0324]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0324 : work0324.theta.ok = true ∧
    work0324.jac.invOK = true ∧ acceptsUnitSq work0324.out = true := by
  norm_num [work0324, contact0324, tau0324, center0324, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0324 : CellCertificate where
  tauBall := tau0324
  contactCenter := center0324
  contactBall := contact0324
  work := work0324
  center_sq := center_sq0324
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0324.1
  jac_ok := checks0324.2.1
  accepted := checks0324.2.2

def tau0325 : RatBall :=
  ⟨⟨3/80, 17/80⟩, 3/160⟩
def center0325 : GaussianRat :=
  ⟨13627917/500000000, 149428611/1000000000⟩
def contact0325 : RatBall := localContactBall tau0325 center0325
def work0325 : RoundedTauEval :=
  evalTau precision tau0325 contact0325 logTwoBall

theorem center_sq0325 : (center0325.re : ℝ)^2 +
    (center0325.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0325]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0325 : work0325.theta.ok = true ∧
    work0325.jac.invOK = true ∧ acceptsUnitSq work0325.out = true := by
  norm_num [work0325, contact0325, tau0325, center0325, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0325 : CellCertificate where
  tauBall := tau0325
  contactCenter := center0325
  contactBall := contact0325
  work := work0325
  center_sq := center_sq0325
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0325.1
  jac_ok := checks0325.2.1
  accepted := checks0325.2.2

def tau0326 : RatBall :=
  ⟨⟨1/80, 19/80⟩, 3/160⟩
def center0326 : GaussianRat :=
  ⟨1150363/125000000, 41981661/250000000⟩
def contact0326 : RatBall := localContactBall tau0326 center0326
def work0326 : RoundedTauEval :=
  evalTau precision tau0326 contact0326 logTwoBall

theorem center_sq0326 : (center0326.re : ℝ)^2 +
    (center0326.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0326]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0326 : work0326.theta.ok = true ∧
    work0326.jac.invOK = true ∧ acceptsUnitSq work0326.out = true := by
  norm_num [work0326, contact0326, tau0326, center0326, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0326 : CellCertificate where
  tauBall := tau0326
  contactCenter := center0326
  contactBall := contact0326
  work := work0326
  center_sq := center_sq0326
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0326.1
  jac_ok := checks0326.2.1
  accepted := checks0326.2.2

def tau0327 : RatBall :=
  ⟨⟨3/80, 19/80⟩, 3/160⟩
def center0327 : GaussianRat :=
  ⟨551859/20000000, 167686167/1000000000⟩
def contact0327 : RatBall := localContactBall tau0327 center0327
def work0327 : RoundedTauEval :=
  evalTau precision tau0327 contact0327 logTwoBall

theorem center_sq0327 : (center0327.re : ℝ)^2 +
    (center0327.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0327]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0327 : work0327.theta.ok = true ∧
    work0327.jac.invOK = true ∧ acceptsUnitSq work0327.out = true := by
  norm_num [work0327, contact0327, tau0327, center0327, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0327 : CellCertificate where
  tauBall := tau0327
  contactCenter := center0327
  contactBall := contact0327
  work := work0327
  center_sq := center_sq0327
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0327.1
  jac_ok := checks0327.2.1
  accepted := checks0327.2.2

def cells : List CellCertificate := [cell0320, cell0321, cell0322, cell0323, cell0324, cell0325, cell0326, cell0327]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040
