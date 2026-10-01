import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2776 : RatBall :=
  ⟨⟨-39/640, -253/640⟩, 3/1280⟩
def center2776 : GaussianRat :=
  ⟨-50272091/1000000000, -144484349/500000000⟩
def contact2776 : RatBall := localContactBall tau2776 center2776
def work2776 : RoundedTauEval :=
  evalTau precision tau2776 contact2776 logTwoBall

theorem center_sq2776 : (center2776.re : ℝ)^2 +
    (center2776.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2776]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2776 : work2776.theta.ok = true ∧
    work2776.jac.invOK = true ∧ acceptsUnitSq work2776.out = true := by
  norm_num [work2776, contact2776, tau2776, center2776, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2776 : CellCertificate where
  tauBall := tau2776
  contactCenter := center2776
  contactBall := contact2776
  work := work2776
  center_sq := center_sq2776
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2776.1
  jac_ok := checks2776.2.1
  accepted := checks2776.2.2

def tau2777 : RatBall :=
  ⟨⟨-37/640, -253/640⟩, 3/1280⟩
def center2777 : GaussianRat :=
  ⟨-47706761/1000000000, -36139591/125000000⟩
def contact2777 : RatBall := localContactBall tau2777 center2777
def work2777 : RoundedTauEval :=
  evalTau precision tau2777 contact2777 logTwoBall

theorem center_sq2777 : (center2777.re : ℝ)^2 +
    (center2777.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2777]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2777 : work2777.theta.ok = true ∧
    work2777.jac.invOK = true ∧ acceptsUnitSq work2777.out = true := by
  norm_num [work2777, contact2777, tau2777, center2777, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2777 : CellCertificate where
  tauBall := tau2777
  contactCenter := center2777
  contactBall := contact2777
  work := work2777
  center_sq := center_sq2777
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2777.1
  jac_ok := checks2777.2.1
  accepted := checks2777.2.2

def tau2778 : RatBall :=
  ⟨⟨-7/128, -253/640⟩, 3/1280⟩
def center2778 : GaussianRat :=
  ⟨-9027887/200000000, -289257137/1000000000⟩
def contact2778 : RatBall := localContactBall tau2778 center2778
def work2778 : RoundedTauEval :=
  evalTau precision tau2778 contact2778 logTwoBall

theorem center_sq2778 : (center2778.re : ℝ)^2 +
    (center2778.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2778]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2778 : work2778.theta.ok = true ∧
    work2778.jac.invOK = true ∧ acceptsUnitSq work2778.out = true := by
  norm_num [work2778, contact2778, tau2778, center2778, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2778 : CellCertificate where
  tauBall := tau2778
  contactCenter := center2778
  contactBall := contact2778
  work := work2778
  center_sq := center_sq2778
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2778.1
  jac_ok := checks2778.2.1
  accepted := checks2778.2.2

def tau2779 : RatBall :=
  ⟨⟨-33/640, -253/640⟩, 3/1280⟩
def center2779 : GaussianRat :=
  ⟨-42570217/1000000000, -144694949/500000000⟩
def contact2779 : RatBall := localContactBall tau2779 center2779
def work2779 : RoundedTauEval :=
  evalTau precision tau2779 contact2779 logTwoBall

theorem center_sq2779 : (center2779.re : ℝ)^2 +
    (center2779.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2779]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2779 : work2779.theta.ok = true ∧
    work2779.jac.invOK = true ∧ acceptsUnitSq work2779.out = true := by
  norm_num [work2779, contact2779, tau2779, center2779, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2779 : CellCertificate where
  tauBall := tau2779
  contactCenter := center2779
  contactBall := contact2779
  work := work2779
  center_sq := center_sq2779
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2779.1
  jac_ok := checks2779.2.1
  accepted := checks2779.2.2

def tau2780 : RatBall :=
  ⟨⟨-39/640, -251/640⟩, 3/1280⟩
def center2780 : GaussianRat :=
  ⟨-10024261/200000000, -14320409/50000000⟩
def contact2780 : RatBall := localContactBall tau2780 center2780
def work2780 : RoundedTauEval :=
  evalTau precision tau2780 contact2780 logTwoBall

theorem center_sq2780 : (center2780.re : ℝ)^2 +
    (center2780.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2780]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2780 : work2780.theta.ok = true ∧
    work2780.jac.invOK = true ∧ acceptsUnitSq work2780.out = true := by
  norm_num [work2780, contact2780, tau2780, center2780, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2780 : CellCertificate where
  tauBall := tau2780
  contactCenter := center2780
  contactBall := contact2780
  work := work2780
  center_sq := center_sq2780
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2780.1
  jac_ok := checks2780.2.1
  accepted := checks2780.2.2

def tau2781 : RatBall :=
  ⟨⟨-37/640, -251/640⟩, 3/1280⟩
def center2781 : GaussianRat :=
  ⟨-4756353/100000000, -4477409/15625000⟩
def contact2781 : RatBall := localContactBall tau2781 center2781
def work2781 : RoundedTauEval :=
  evalTau precision tau2781 contact2781 logTwoBall

theorem center_sq2781 : (center2781.re : ℝ)^2 +
    (center2781.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2781]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2781 : work2781.theta.ok = true ∧
    work2781.jac.invOK = true ∧ acceptsUnitSq work2781.out = true := by
  norm_num [work2781, contact2781, tau2781, center2781, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2781 : CellCertificate where
  tauBall := tau2781
  contactCenter := center2781
  contactBall := contact2781
  work := work2781
  center_sq := center_sq2781
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2781.1
  jac_ok := checks2781.2.1
  accepted := checks2781.2.2

def tau2782 : RatBall :=
  ⟨⟨-39/640, -249/640⟩, 3/1280⟩
def center2782 : GaussianRat :=
  ⟨-4997259/100000000, -17740947/62500000⟩
def contact2782 : RatBall := localContactBall tau2782 center2782
def work2782 : RoundedTauEval :=
  evalTau precision tau2782 contact2782 logTwoBall

theorem center_sq2782 : (center2782.re : ℝ)^2 +
    (center2782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2782 : work2782.theta.ok = true ∧
    work2782.jac.invOK = true ∧ acceptsUnitSq work2782.out = true := by
  norm_num [work2782, contact2782, tau2782, center2782, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2782 : CellCertificate where
  tauBall := tau2782
  contactCenter := center2782
  contactBall := contact2782
  work := work2782
  center_sq := center_sq2782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2782.1
  jac_ok := checks2782.2.1
  accepted := checks2782.2.2

def tau2783 : RatBall :=
  ⟨⟨-37/640, -249/640⟩, 3/1280⟩
def center2783 : GaussianRat :=
  ⟨-11855567/250000000, -283999143/1000000000⟩
def contact2783 : RatBall := localContactBall tau2783 center2783
def work2783 : RoundedTauEval :=
  evalTau precision tau2783 contact2783 logTwoBall

theorem center_sq2783 : (center2783.re : ℝ)^2 +
    (center2783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2783 : work2783.theta.ok = true ∧
    work2783.jac.invOK = true ∧ acceptsUnitSq work2783.out = true := by
  norm_num [work2783, contact2783, tau2783, center2783, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2783 : CellCertificate where
  tauBall := tau2783
  contactCenter := center2783
  contactBall := contact2783
  work := work2783
  center_sq := center_sq2783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2783.1
  jac_ok := checks2783.2.1
  accepted := checks2783.2.2

def cells : List CellCertificate := [cell2776, cell2777, cell2778, cell2779, cell2780, cell2781, cell2782, cell2783]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347
