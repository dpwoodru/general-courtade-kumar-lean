import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0264 : RatBall :=
  ⟨⟨-1/80, 19/80⟩, 3/160⟩
def center0264 : GaussianRat :=
  ⟨-1150363/125000000, 41981661/250000000⟩
def contact0264 : RatBall := localContactBall tau0264 center0264
def work0264 : RoundedTauEval :=
  evalTau precision tau0264 contact0264 logTwoBall

theorem center_sq0264 : (center0264.re : ℝ)^2 +
    (center0264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0264 : work0264.theta.ok = true ∧
    work0264.jac.invOK = true ∧ acceptsUnitSq work0264.out = true := by
  norm_num [work0264, contact0264, tau0264, center0264, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0264 : CellCertificate where
  tauBall := tau0264
  contactCenter := center0264
  contactBall := contact0264
  work := work0264
  center_sq := center_sq0264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0264.1
  jac_ok := checks0264.2.1
  accepted := checks0264.2.2

def tau0265 : RatBall :=
  ⟨⟨-7/80, 21/80⟩, 3/160⟩
def center0265 : GaussianRat :=
  ⟨-6508393/100000000, 184829567/1000000000⟩
def contact0265 : RatBall := localContactBall tau0265 center0265
def work0265 : RoundedTauEval :=
  evalTau precision tau0265 contact0265 logTwoBall

theorem center_sq0265 : (center0265.re : ℝ)^2 +
    (center0265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0265 : work0265.theta.ok = true ∧
    work0265.jac.invOK = true ∧ acceptsUnitSq work0265.out = true := by
  norm_num [work0265, contact0265, tau0265, center0265, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0265 : CellCertificate where
  tauBall := tau0265
  contactCenter := center0265
  contactBall := contact0265
  work := work0265
  center_sq := center_sq0265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0265.1
  jac_ok := checks0265.2.1
  accepted := checks0265.2.2

def tau0266 : RatBall :=
  ⟨⟨-1/16, 21/80⟩, 3/160⟩
def center0266 : GaussianRat :=
  ⟨-46572457/1000000000, 46409673/250000000⟩
def contact0266 : RatBall := localContactBall tau0266 center0266
def work0266 : RoundedTauEval :=
  evalTau precision tau0266 contact0266 logTwoBall

theorem center_sq0266 : (center0266.re : ℝ)^2 +
    (center0266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0266 : work0266.theta.ok = true ∧
    work0266.jac.invOK = true ∧ acceptsUnitSq work0266.out = true := by
  norm_num [work0266, contact0266, tau0266, center0266, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0266 : CellCertificate where
  tauBall := tau0266
  contactCenter := center0266
  contactBall := contact0266
  work := work0266
  center_sq := center_sq0266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0266.1
  jac_ok := checks0266.2.1
  accepted := checks0266.2.2

def tau0267 : RatBall :=
  ⟨⟨-3/80, 21/80⟩, 3/160⟩
def center0267 : GaussianRat :=
  ⟨-27977261/1000000000, 186182371/1000000000⟩
def contact0267 : RatBall := localContactBall tau0267 center0267
def work0267 : RoundedTauEval :=
  evalTau precision tau0267 contact0267 logTwoBall

theorem center_sq0267 : (center0267.re : ℝ)^2 +
    (center0267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0267 : work0267.theta.ok = true ∧
    work0267.jac.invOK = true ∧ acceptsUnitSq work0267.out = true := by
  norm_num [work0267, contact0267, tau0267, center0267, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0267 : CellCertificate where
  tauBall := tau0267
  contactCenter := center0267
  contactBall := contact0267
  work := work0267
  center_sq := center_sq0267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0267.1
  jac_ok := checks0267.2.1
  accepted := checks0267.2.2

def tau0268 : RatBall :=
  ⟨⟨-1/80, 21/80⟩, 3/160⟩
def center0268 : GaussianRat :=
  ⟨-4665703/500000000, 93227751/500000000⟩
def contact0268 : RatBall := localContactBall tau0268 center0268
def work0268 : RoundedTauEval :=
  evalTau precision tau0268 contact0268 logTwoBall

theorem center_sq0268 : (center0268.re : ℝ)^2 +
    (center0268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0268 : work0268.theta.ok = true ∧
    work0268.jac.invOK = true ∧ acceptsUnitSq work0268.out = true := by
  norm_num [work0268, contact0268, tau0268, center0268, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0268 : CellCertificate where
  tauBall := tau0268
  contactCenter := center0268
  contactBall := contact0268
  work := work0268
  center_sq := center_sq0268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0268.1
  jac_ok := checks0268.2.1
  accepted := checks0268.2.2

def tau0269 : RatBall :=
  ⟨⟨-3/80, 23/80⟩, 3/160⟩
def center0269 : GaussianRat :=
  ⟨-14206169/500000000, 204949543/1000000000⟩
def contact0269 : RatBall := localContactBall tau0269 center0269
def work0269 : RoundedTauEval :=
  evalTau precision tau0269 contact0269 logTwoBall

theorem center_sq0269 : (center0269.re : ℝ)^2 +
    (center0269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0269 : work0269.theta.ok = true ∧
    work0269.jac.invOK = true ∧ acceptsUnitSq work0269.out = true := by
  norm_num [work0269, contact0269, tau0269, center0269, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0269 : CellCertificate where
  tauBall := tau0269
  contactCenter := center0269
  contactBall := contact0269
  work := work0269
  center_sq := center_sq0269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0269.1
  jac_ok := checks0269.2.1
  accepted := checks0269.2.2

def tau0270 : RatBall :=
  ⟨⟨-1/80, 23/80⟩, 3/160⟩
def center0270 : GaussianRat :=
  ⟨-4738451/500000000, 102628961/500000000⟩
def contact0270 : RatBall := localContactBall tau0270 center0270
def work0270 : RoundedTauEval :=
  evalTau precision tau0270 contact0270 logTwoBall

theorem center_sq0270 : (center0270.re : ℝ)^2 +
    (center0270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0270 : work0270.theta.ok = true ∧
    work0270.jac.invOK = true ∧ acceptsUnitSq work0270.out = true := by
  norm_num [work0270, contact0270, tau0270, center0270, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0270 : CellCertificate where
  tauBall := tau0270
  contactCenter := center0270
  contactBall := contact0270
  work := work0270
  center_sq := center_sq0270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0270.1
  jac_ok := checks0270.2.1
  accepted := checks0270.2.2

def tau0271 : RatBall :=
  ⟨⟨1/16, 13/80⟩, 3/160⟩
def center0271 : GaussianRat :=
  ⟨44475471/1000000000, 14150393/125000000⟩
def contact0271 : RatBall := localContactBall tau0271 center0271
def work0271 : RoundedTauEval :=
  evalTau precision tau0271 contact0271 logTwoBall

theorem center_sq0271 : (center0271.re : ℝ)^2 +
    (center0271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0271 : work0271.theta.ok = true ∧
    work0271.jac.invOK = true ∧ acceptsUnitSq work0271.out = true := by
  norm_num [work0271, contact0271, tau0271, center0271, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0271 : CellCertificate where
  tauBall := tau0271
  contactCenter := center0271
  contactBall := contact0271
  work := work0271
  center_sq := center_sq0271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0271.1
  jac_ok := checks0271.2.1
  accepted := checks0271.2.2

def cells : List CellCertificate := [cell0264, cell0265, cell0266, cell0267, cell0268, cell0269, cell0270, cell0271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033
