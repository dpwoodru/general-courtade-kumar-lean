import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1192 : RatBall :=
  ⟨⟨41/160, 41/160⟩, 3/320⟩
def center1192 : GaussianRat :=
  ⟨184996961/1000000000, 21119029/125000000⟩
def contact1192 : RatBall := localContactBall tau1192 center1192
def work1192 : RoundedTauEval :=
  evalTau precision tau1192 contact1192 logTwoBall

theorem center_sq1192 : (center1192.re : ℝ)^2 +
    (center1192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1192 : work1192.theta.ok = true ∧
    work1192.jac.invOK = true ∧ acceptsUnitSq work1192.out = true := by
  norm_num [work1192, contact1192, tau1192, center1192, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1192 : CellCertificate where
  tauBall := tau1192
  contactCenter := center1192
  contactBall := contact1192
  work := work1192
  center_sq := center_sq1192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1192.1
  jac_ok := checks1192.2.1
  accepted := checks1192.2.2

def tau1193 : RatBall :=
  ⟨⟨43/160, 41/160⟩, 3/320⟩
def center1193 : GaussianRat :=
  ⟨193470247/1000000000, 167770653/1000000000⟩
def contact1193 : RatBall := localContactBall tau1193 center1193
def work1193 : RoundedTauEval :=
  evalTau precision tau1193 contact1193 logTwoBall

theorem center_sq1193 : (center1193.re : ℝ)^2 +
    (center1193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1193 : work1193.theta.ok = true ∧
    work1193.jac.invOK = true ∧ acceptsUnitSq work1193.out = true := by
  norm_num [work1193, contact1193, tau1193, center1193, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1193 : CellCertificate where
  tauBall := tau1193
  contactCenter := center1193
  contactBall := contact1193
  work := work1193
  center_sq := center_sq1193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1193.1
  jac_ok := checks1193.2.1
  accepted := checks1193.2.2

def tau1194 : RatBall :=
  ⟨⟨49/160, 33/160⟩, 3/320⟩
def center1194 : GaussianRat :=
  ⟨8553183/40000000, 26276749/200000000⟩
def contact1194 : RatBall := localContactBall tau1194 center1194
def work1194 : RoundedTauEval :=
  evalTau precision tau1194 contact1194 logTwoBall

theorem center_sq1194 : (center1194.re : ℝ)^2 +
    (center1194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1194 : work1194.theta.ok = true ∧
    work1194.jac.invOK = true ∧ acceptsUnitSq work1194.out = true := by
  norm_num [work1194, contact1194, tau1194, center1194, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1194 : CellCertificate where
  tauBall := tau1194
  contactCenter := center1194
  contactBall := contact1194
  work := work1194
  center_sq := center_sq1194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1194.1
  jac_ok := checks1194.2.1
  accepted := checks1194.2.2

def tau1195 : RatBall :=
  ⟨⟨51/160, 33/160⟩, 3/320⟩
def center1195 : GaussianRat :=
  ⟨13868507/62500000, 13035901/100000000⟩
def contact1195 : RatBall := localContactBall tau1195 center1195
def work1195 : RoundedTauEval :=
  evalTau precision tau1195 contact1195 logTwoBall

theorem center_sq1195 : (center1195.re : ℝ)^2 +
    (center1195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1195 : work1195.theta.ok = true ∧
    work1195.jac.invOK = true ∧ acceptsUnitSq work1195.out = true := by
  norm_num [work1195, contact1195, tau1195, center1195, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1195 : CellCertificate where
  tauBall := tau1195
  contactCenter := center1195
  contactBall := contact1195
  work := work1195
  center_sq := center_sq1195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1195.1
  jac_ok := checks1195.2.1
  accepted := checks1195.2.2

def tau1196 : RatBall :=
  ⟨⟨49/160, 7/32⟩, 3/320⟩
def center1196 : GaussianRat :=
  ⟨26859619/125000000, 139498183/1000000000⟩
def contact1196 : RatBall := localContactBall tau1196 center1196
def work1196 : RoundedTauEval :=
  evalTau precision tau1196 contact1196 logTwoBall

theorem center_sq1196 : (center1196.re : ℝ)^2 +
    (center1196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1196 : work1196.theta.ok = true ∧
    work1196.jac.invOK = true ∧ acceptsUnitSq work1196.out = true := by
  norm_num [work1196, contact1196, tau1196, center1196, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1196 : CellCertificate where
  tauBall := tau1196
  contactCenter := center1196
  contactBall := contact1196
  work := work1196
  center_sq := center_sq1196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1196.1
  jac_ok := checks1196.2.1
  accepted := checks1196.2.2

def tau1197 : RatBall :=
  ⟨⟨51/160, 7/32⟩, 3/320⟩
def center1197 : GaussianRat :=
  ⟨111484361/500000000, 13840239/100000000⟩
def contact1197 : RatBall := localContactBall tau1197 center1197
def work1197 : RoundedTauEval :=
  evalTau precision tau1197 contact1197 logTwoBall

theorem center_sq1197 : (center1197.re : ℝ)^2 +
    (center1197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1197]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1197 : work1197.theta.ok = true ∧
    work1197.jac.invOK = true ∧ acceptsUnitSq work1197.out = true := by
  norm_num [work1197, contact1197, tau1197, center1197, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1197 : CellCertificate where
  tauBall := tau1197
  contactCenter := center1197
  contactBall := contact1197
  work := work1197
  center_sq := center_sq1197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1197.1
  jac_ok := checks1197.2.1
  accepted := checks1197.2.2

def tau1198 : RatBall :=
  ⟨⟨53/160, 33/160⟩, 3/320⟩
def center1198 : GaussianRat :=
  ⟨114945839/500000000, 32327639/250000000⟩
def contact1198 : RatBall := localContactBall tau1198 center1198
def work1198 : RoundedTauEval :=
  evalTau precision tau1198 contact1198 logTwoBall

theorem center_sq1198 : (center1198.re : ℝ)^2 +
    (center1198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1198 : work1198.theta.ok = true ∧
    work1198.jac.invOK = true ∧ acceptsUnitSq work1198.out = true := by
  norm_num [work1198, contact1198, tau1198, center1198, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1198 : CellCertificate where
  tauBall := tau1198
  contactCenter := center1198
  contactBall := contact1198
  work := work1198
  center_sq := center_sq1198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1198.1
  jac_ok := checks1198.2.1
  accepted := checks1198.2.2

def tau1199 : RatBall :=
  ⟨⟨49/160, 37/160⟩, 3/320⟩
def center1199 : GaussianRat :=
  ⟨8639819/40000000, 36909857/250000000⟩
def contact1199 : RatBall := localContactBall tau1199 center1199
def work1199 : RoundedTauEval :=
  evalTau precision tau1199 contact1199 logTwoBall

theorem center_sq1199 : (center1199.re : ℝ)^2 +
    (center1199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1199 : work1199.theta.ok = true ∧
    work1199.jac.invOK = true ∧ acceptsUnitSq work1199.out = true := by
  norm_num [work1199, contact1199, tau1199, center1199, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1199 : CellCertificate where
  tauBall := tau1199
  contactCenter := center1199
  contactBall := contact1199
  work := work1199
  center_sq := center_sq1199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1199.1
  jac_ok := checks1199.2.1
  accepted := checks1199.2.2

def cells : List CellCertificate := [cell1192, cell1193, cell1194, cell1195, cell1196, cell1197, cell1198, cell1199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149
