import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0370

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2960 : RatBall :=
  ⟨⟨33/640, -253/640⟩, 3/1280⟩
def center2960 : GaussianRat :=
  ⟨42570217/1000000000, -144694949/500000000⟩
def contact2960 : RatBall := localContactBall tau2960 center2960
def work2960 : RoundedTauEval :=
  evalTau precision tau2960 contact2960 logTwoBall

theorem center_sq2960 : (center2960.re : ℝ)^2 +
    (center2960.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2960]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2960 : work2960.theta.ok = true ∧
    work2960.jac.invOK = true ∧ acceptsUnitSq work2960.out = true := by
  norm_num [work2960, contact2960, tau2960, center2960, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2960 : CellCertificate where
  tauBall := tau2960
  contactCenter := center2960
  contactBall := contact2960
  work := work2960
  center_sq := center_sq2960
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2960.1
  jac_ok := checks2960.2.1
  accepted := checks2960.2.2

def tau2961 : RatBall :=
  ⟨⟨7/128, -253/640⟩, 3/1280⟩
def center2961 : GaussianRat :=
  ⟨9027887/200000000, -289257137/1000000000⟩
def contact2961 : RatBall := localContactBall tau2961 center2961
def work2961 : RoundedTauEval :=
  evalTau precision tau2961 contact2961 logTwoBall

theorem center_sq2961 : (center2961.re : ℝ)^2 +
    (center2961.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2961]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2961 : work2961.theta.ok = true ∧
    work2961.jac.invOK = true ∧ acceptsUnitSq work2961.out = true := by
  norm_num [work2961, contact2961, tau2961, center2961, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2961 : CellCertificate where
  tauBall := tau2961
  contactCenter := center2961
  contactBall := contact2961
  work := work2961
  center_sq := center_sq2961
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2961.1
  jac_ok := checks2961.2.1
  accepted := checks2961.2.2

def tau2962 : RatBall :=
  ⟨⟨37/640, -253/640⟩, 3/1280⟩
def center2962 : GaussianRat :=
  ⟨47706761/1000000000, -36139591/125000000⟩
def contact2962 : RatBall := localContactBall tau2962 center2962
def work2962 : RoundedTauEval :=
  evalTau precision tau2962 contact2962 logTwoBall

theorem center_sq2962 : (center2962.re : ℝ)^2 +
    (center2962.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2962]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2962 : work2962.theta.ok = true ∧
    work2962.jac.invOK = true ∧ acceptsUnitSq work2962.out = true := by
  norm_num [work2962, contact2962, tau2962, center2962, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2962 : CellCertificate where
  tauBall := tau2962
  contactCenter := center2962
  contactBall := contact2962
  work := work2962
  center_sq := center_sq2962
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2962.1
  jac_ok := checks2962.2.1
  accepted := checks2962.2.2

def tau2963 : RatBall :=
  ⟨⟨39/640, -253/640⟩, 3/1280⟩
def center2963 : GaussianRat :=
  ⟨50272091/1000000000, -144484349/500000000⟩
def contact2963 : RatBall := localContactBall tau2963 center2963
def work2963 : RoundedTauEval :=
  evalTau precision tau2963 contact2963 logTwoBall

theorem center_sq2963 : (center2963.re : ℝ)^2 +
    (center2963.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2963]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2963 : work2963.theta.ok = true ∧
    work2963.jac.invOK = true ∧ acceptsUnitSq work2963.out = true := by
  norm_num [work2963, contact2963, tau2963, center2963, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2963 : CellCertificate where
  tauBall := tau2963
  contactCenter := center2963
  contactBall := contact2963
  work := work2963
  center_sq := center_sq2963
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2963.1
  jac_ok := checks2963.2.1
  accepted := checks2963.2.2

def tau2964 : RatBall :=
  ⟨⟨33/640, -251/640⟩, 3/1280⟩
def center2964 : GaussianRat :=
  ⟨42442179/1000000000, -286823589/1000000000⟩
def contact2964 : RatBall := localContactBall tau2964 center2964
def work2964 : RoundedTauEval :=
  evalTau precision tau2964 contact2964 logTwoBall

theorem center_sq2964 : (center2964.re : ℝ)^2 +
    (center2964.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2964]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2964 : work2964.theta.ok = true ∧
    work2964.jac.invOK = true ∧ acceptsUnitSq work2964.out = true := by
  norm_num [work2964, contact2964, tau2964, center2964, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2964 : CellCertificate where
  tauBall := tau2964
  contactCenter := center2964
  contactBall := contact2964
  work := work2964
  center_sq := center_sq2964
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2964.1
  jac_ok := checks2964.2.1
  accepted := checks2964.2.2

def tau2965 : RatBall :=
  ⟨⟨7/128, -251/640⟩, 3/1280⟩
def center2965 : GaussianRat :=
  ⟨45003787/1000000000, -57338531/200000000⟩
def contact2965 : RatBall := localContactBall tau2965 center2965
def work2965 : RoundedTauEval :=
  evalTau precision tau2965 contact2965 logTwoBall

theorem center_sq2965 : (center2965.re : ℝ)^2 +
    (center2965.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2965]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2965 : work2965.theta.ok = true ∧
    work2965.jac.invOK = true ∧ acceptsUnitSq work2965.out = true := by
  norm_num [work2965, contact2965, tau2965, center2965, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2965 : CellCertificate where
  tauBall := tau2965
  contactCenter := center2965
  contactBall := contact2965
  work := work2965
  center_sq := center_sq2965
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2965.1
  jac_ok := checks2965.2.1
  accepted := checks2965.2.2

def tau2966 : RatBall :=
  ⟨⟨33/640, -249/640⟩, 3/1280⟩
def center2966 : GaussianRat :=
  ⟨42315903/1000000000, -284264849/1000000000⟩
def contact2966 : RatBall := localContactBall tau2966 center2966
def work2966 : RoundedTauEval :=
  evalTau precision tau2966 contact2966 logTwoBall

theorem center_sq2966 : (center2966.re : ℝ)^2 +
    (center2966.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2966]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2966 : work2966.theta.ok = true ∧
    work2966.jac.invOK = true ∧ acceptsUnitSq work2966.out = true := by
  norm_num [work2966, contact2966, tau2966, center2966, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2966 : CellCertificate where
  tauBall := tau2966
  contactCenter := center2966
  contactBall := contact2966
  work := work2966
  center_sq := center_sq2966
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2966.1
  jac_ok := checks2966.2.1
  accepted := checks2966.2.2

def tau2967 : RatBall :=
  ⟨⟨7/128, -249/640⟩, 3/1280⟩
def center2967 : GaussianRat :=
  ⟨22435003/500000000, -284135717/1000000000⟩
def contact2967 : RatBall := localContactBall tau2967 center2967
def work2967 : RoundedTauEval :=
  evalTau precision tau2967 contact2967 logTwoBall

theorem center_sq2967 : (center2967.re : ℝ)^2 +
    (center2967.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2967]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2967 : work2967.theta.ok = true ∧
    work2967.jac.invOK = true ∧ acceptsUnitSq work2967.out = true := by
  norm_num [work2967, contact2967, tau2967, center2967, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2967 : CellCertificate where
  tauBall := tau2967
  contactCenter := center2967
  contactBall := contact2967
  work := work2967
  center_sq := center_sq2967
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2967.1
  jac_ok := checks2967.2.1
  accepted := checks2967.2.2

def cells : List CellCertificate := [cell2960, cell2961, cell2962, cell2963, cell2964, cell2965, cell2966, cell2967]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0370
