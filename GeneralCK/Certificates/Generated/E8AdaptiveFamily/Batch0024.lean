import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0192 : RatBall :=
  ⟨⟨27/80, -3/80⟩, 3/160⟩
def center0192 : GaussianRat :=
  ⟨225572371/1000000000, -4648277/200000000⟩
def contact0192 : RatBall := localContactBall tau0192 center0192
def work0192 : RoundedTauEval :=
  evalTau precision tau0192 contact0192 logTwoBall

theorem center_sq0192 : (center0192.re : ℝ)^2 +
    (center0192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0192 : work0192.theta.ok = true ∧
    work0192.jac.invOK = true ∧ acceptsUnitSq work0192.out = true := by
  norm_num [work0192, contact0192, tau0192, center0192, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0192 : CellCertificate where
  tauBall := tau0192
  contactCenter := center0192
  contactBall := contact0192
  work := work0192
  center_sq := center_sq0192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0192.1
  jac_ok := checks0192.2.1
  accepted := checks0192.2.2

def tau0193 : RatBall :=
  ⟨⟨5/16, -1/80⟩, 3/160⟩
def center0193 : GaussianRat :=
  ⟨104858117/500000000, -3932321/500000000⟩
def contact0193 : RatBall := localContactBall tau0193 center0193
def work0193 : RoundedTauEval :=
  evalTau precision tau0193 contact0193 logTwoBall

theorem center_sq0193 : (center0193.re : ℝ)^2 +
    (center0193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0193 : work0193.theta.ok = true ∧
    work0193.jac.invOK = true ∧ acceptsUnitSq work0193.out = true := by
  norm_num [work0193, contact0193, tau0193, center0193, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0193 : CellCertificate where
  tauBall := tau0193
  contactCenter := center0193
  contactBall := contact0193
  work := work0193
  center_sq := center_sq0193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0193.1
  jac_ok := checks0193.2.1
  accepted := checks0193.2.2

def tau0194 : RatBall :=
  ⟨⟨27/80, -1/80⟩, 3/160⟩
def center0194 : GaussianRat :=
  ⟨45065623/200000000, -7745371/1000000000⟩
def contact0194 : RatBall := localContactBall tau0194 center0194
def work0194 : RoundedTauEval :=
  evalTau precision tau0194 contact0194 logTwoBall

theorem center_sq0194 : (center0194.re : ℝ)^2 +
    (center0194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0194 : work0194.theta.ok = true ∧
    work0194.jac.invOK = true ∧ acceptsUnitSq work0194.out = true := by
  norm_num [work0194, contact0194, tau0194, center0194, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0194 : CellCertificate where
  tauBall := tau0194
  contactCenter := center0194
  contactBall := contact0194
  work := work0194
  center_sq := center_sq0194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0194.1
  jac_ok := checks0194.2.1
  accepted := checks0194.2.2

def tau0195 : RatBall :=
  ⟨⟨29/80, -3/80⟩, 3/160⟩
def center0195 : GaussianRat :=
  ⟨120475049/500000000, -4573419/200000000⟩
def contact0195 : RatBall := localContactBall tau0195 center0195
def work0195 : RoundedTauEval :=
  evalTau precision tau0195 contact0195 logTwoBall

theorem center_sq0195 : (center0195.re : ℝ)^2 +
    (center0195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0195 : work0195.theta.ok = true ∧
    work0195.jac.invOK = true ∧ acceptsUnitSq work0195.out = true := by
  norm_num [work0195, contact0195, tau0195, center0195, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0195 : CellCertificate where
  tauBall := tau0195
  contactCenter := center0195
  contactBall := contact0195
  work := work0195
  center_sq := center_sq0195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0195.1
  jac_ok := checks0195.2.1
  accepted := checks0195.2.2

def tau0196 : RatBall :=
  ⟨⟨29/80, -1/80⟩, 3/160⟩
def center0196 : GaussianRat :=
  ⟨240695961/1000000000, -1905207/250000000⟩
def contact0196 : RatBall := localContactBall tau0196 center0196
def work0196 : RoundedTauEval :=
  evalTau precision tau0196 contact0196 logTwoBall

theorem center_sq0196 : (center0196.re : ℝ)^2 +
    (center0196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0196 : work0196.theta.ok = true ∧
    work0196.jac.invOK = true ∧ acceptsUnitSq work0196.out = true := by
  norm_num [work0196, contact0196, tau0196, center0196, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0196 : CellCertificate where
  tauBall := tau0196
  contactCenter := center0196
  contactBall := contact0196
  work := work0196
  center_sq := center_sq0196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0196.1
  jac_ok := checks0196.2.1
  accepted := checks0196.2.2

def tau0197 : RatBall :=
  ⟨⟨31/80, -1/80⟩, 3/160⟩
def center0197 : GaussianRat :=
  ⟨255809887/1000000000, -749167/100000000⟩
def contact0197 : RatBall := localContactBall tau0197 center0197
def work0197 : RoundedTauEval :=
  evalTau precision tau0197 contact0197 logTwoBall

theorem center_sq0197 : (center0197.re : ℝ)^2 +
    (center0197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0197]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0197 : work0197.theta.ok = true ∧
    work0197.jac.invOK = true ∧ acceptsUnitSq work0197.out = true := by
  norm_num [work0197, contact0197, tau0197, center0197, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0197 : CellCertificate where
  tauBall := tau0197
  contactCenter := center0197
  contactBall := contact0197
  work := work0197
  center_sq := center_sq0197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0197.1
  jac_ok := checks0197.2.1
  accepted := checks0197.2.2

def tau0198 : RatBall :=
  ⟨⟨-31/80, 1/80⟩, 3/160⟩
def center0198 : GaussianRat :=
  ⟨-255809887/1000000000, 749167/100000000⟩
def contact0198 : RatBall := localContactBall tau0198 center0198
def work0198 : RoundedTauEval :=
  evalTau precision tau0198 contact0198 logTwoBall

theorem center_sq0198 : (center0198.re : ℝ)^2 +
    (center0198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0198 : work0198.theta.ok = true ∧
    work0198.jac.invOK = true ∧ acceptsUnitSq work0198.out = true := by
  norm_num [work0198, contact0198, tau0198, center0198, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0198 : CellCertificate where
  tauBall := tau0198
  contactCenter := center0198
  contactBall := contact0198
  work := work0198
  center_sq := center_sq0198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0198.1
  jac_ok := checks0198.2.1
  accepted := checks0198.2.2

def tau0199 : RatBall :=
  ⟨⟨-29/80, 1/80⟩, 3/160⟩
def center0199 : GaussianRat :=
  ⟨-240695961/1000000000, 1905207/250000000⟩
def contact0199 : RatBall := localContactBall tau0199 center0199
def work0199 : RoundedTauEval :=
  evalTau precision tau0199 contact0199 logTwoBall

theorem center_sq0199 : (center0199.re : ℝ)^2 +
    (center0199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0199 : work0199.theta.ok = true ∧
    work0199.jac.invOK = true ∧ acceptsUnitSq work0199.out = true := by
  norm_num [work0199, contact0199, tau0199, center0199, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0199 : CellCertificate where
  tauBall := tau0199
  contactCenter := center0199
  contactBall := contact0199
  work := work0199
  center_sq := center_sq0199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0199.1
  jac_ok := checks0199.2.1
  accepted := checks0199.2.2

def cells : List CellCertificate := [cell0192, cell0193, cell0194, cell0195, cell0196, cell0197, cell0198, cell0199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024
