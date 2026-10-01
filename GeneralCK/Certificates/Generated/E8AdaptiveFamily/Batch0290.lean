import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0290

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2320 : RatBall :=
  ⟨⟨33/320, 109/320⟩, 3/640⟩
def center2320 : GaussianRat :=
  ⟨20187397/250000000, 48605377/200000000⟩
def contact2320 : RatBall := localContactBall tau2320 center2320
def work2320 : RoundedTauEval :=
  evalTau precision tau2320 contact2320 logTwoBall

theorem center_sq2320 : (center2320.re : ℝ)^2 +
    (center2320.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2320 : work2320.theta.ok = true ∧
    work2320.jac.invOK = true ∧ acceptsUnitSq work2320.out = true := by
  norm_num [work2320, contact2320, tau2320, center2320, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2320 : CellCertificate where
  tauBall := tau2320
  contactCenter := center2320
  contactBall := contact2320
  work := work2320
  center_sq := center_sq2320
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2320.1
  jac_ok := checks2320.2.1
  accepted := checks2320.2.2

def tau2321 : RatBall :=
  ⟨⟨7/64, 109/320⟩, 3/640⟩
def center2321 : GaussianRat :=
  ⟨17115273/200000000, 242620769/1000000000⟩
def contact2321 : RatBall := localContactBall tau2321 center2321
def work2321 : RoundedTauEval :=
  evalTau precision tau2321 contact2321 logTwoBall

theorem center_sq2321 : (center2321.re : ℝ)^2 +
    (center2321.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2321]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2321 : work2321.theta.ok = true ∧
    work2321.jac.invOK = true ∧ acceptsUnitSq work2321.out = true := by
  norm_num [work2321, contact2321, tau2321, center2321, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2321 : CellCertificate where
  tauBall := tau2321
  contactCenter := center2321
  contactBall := contact2321
  work := work2321
  center_sq := center_sq2321
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2321.1
  jac_ok := checks2321.2.1
  accepted := checks2321.2.2

def tau2322 : RatBall :=
  ⟨⟨33/320, 111/320⟩, 3/640⟩
def center2322 : GaussianRat :=
  ⟨20287513/250000000, 247870587/1000000000⟩
def contact2322 : RatBall := localContactBall tau2322 center2322
def work2322 : RoundedTauEval :=
  evalTau precision tau2322 contact2322 logTwoBall

theorem center_sq2322 : (center2322.re : ℝ)^2 +
    (center2322.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2322]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2322 : work2322.theta.ok = true ∧
    work2322.jac.invOK = true ∧ acceptsUnitSq work2322.out = true := by
  norm_num [work2322, contact2322, tau2322, center2322, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2322 : CellCertificate where
  tauBall := tau2322
  contactCenter := center2322
  contactBall := contact2322
  work := work2322
  center_sq := center_sq2322
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2322.1
  jac_ok := checks2322.2.1
  accepted := checks2322.2.2

def tau2323 : RatBall :=
  ⟨⟨7/64, 111/320⟩, 3/640⟩
def center2323 : GaussianRat :=
  ⟨85999463/1000000000, 247453051/1000000000⟩
def contact2323 : RatBall := localContactBall tau2323 center2323
def work2323 : RoundedTauEval :=
  evalTau precision tau2323 contact2323 logTwoBall

theorem center_sq2323 : (center2323.re : ℝ)^2 +
    (center2323.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2323]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2323 : work2323.theta.ok = true ∧
    work2323.jac.invOK = true ∧ acceptsUnitSq work2323.out = true := by
  norm_num [work2323, contact2323, tau2323, center2323, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2323 : CellCertificate where
  tauBall := tau2323
  contactCenter := center2323
  contactBall := contact2323
  work := work2323
  center_sq := center_sq2323
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2323.1
  jac_ok := checks2323.2.1
  accepted := checks2323.2.2

def tau2324 : RatBall :=
  ⟨⟨37/320, 109/320⟩, 3/640⟩
def center2324 : GaussianRat :=
  ⟨45195779/500000000, 121096227/500000000⟩
def contact2324 : RatBall := localContactBall tau2324 center2324
def work2324 : RoundedTauEval :=
  evalTau precision tau2324 contact2324 logTwoBall

theorem center_sq2324 : (center2324.re : ℝ)^2 +
    (center2324.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2324]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2324 : work2324.theta.ok = true ∧
    work2324.jac.invOK = true ∧ acceptsUnitSq work2324.out = true := by
  norm_num [work2324, contact2324, tau2324, center2324, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2324 : CellCertificate where
  tauBall := tau2324
  contactCenter := center2324
  contactBall := contact2324
  work := work2324
  center_sq := center_sq2324
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2324.1
  jac_ok := checks2324.2.1
  accepted := checks2324.2.2

def tau2325 : RatBall :=
  ⟨⟨39/320, 109/320⟩, 3/640⟩
def center2325 : GaussianRat :=
  ⟨47597289/500000000, 241742219/1000000000⟩
def contact2325 : RatBall := localContactBall tau2325 center2325
def work2325 : RoundedTauEval :=
  evalTau precision tau2325 contact2325 logTwoBall

theorem center_sq2325 : (center2325.re : ℝ)^2 +
    (center2325.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2325]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2325 : work2325.theta.ok = true ∧
    work2325.jac.invOK = true ∧ acceptsUnitSq work2325.out = true := by
  norm_num [work2325, contact2325, tau2325, center2325, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2325 : CellCertificate where
  tauBall := tau2325
  contactCenter := center2325
  contactBall := contact2325
  work := work2325
  center_sq := center_sq2325
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2325.1
  jac_ok := checks2325.2.1
  accepted := checks2325.2.2

def tau2326 : RatBall :=
  ⟨⟨37/320, 111/320⟩, 3/640⟩
def center2326 : GaussianRat :=
  ⟨45418507/500000000, 247012717/1000000000⟩
def contact2326 : RatBall := localContactBall tau2326 center2326
def work2326 : RoundedTauEval :=
  evalTau precision tau2326 contact2326 logTwoBall

theorem center_sq2326 : (center2326.re : ℝ)^2 +
    (center2326.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2326]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2326 : work2326.theta.ok = true ∧
    work2326.jac.invOK = true ∧ acceptsUnitSq work2326.out = true := by
  norm_num [work2326, contact2326, tau2326, center2326, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2326 : CellCertificate where
  tauBall := tau2326
  contactCenter := center2326
  contactBall := contact2326
  work := work2326
  center_sq := center_sq2326
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2326.1
  jac_ok := checks2326.2.1
  accepted := checks2326.2.2

def tau2327 : RatBall :=
  ⟨⟨39/320, 111/320⟩, 3/640⟩
def center2327 : GaussianRat :=
  ⟨11957763/125000000, 15409367/62500000⟩
def contact2327 : RatBall := localContactBall tau2327 center2327
def work2327 : RoundedTauEval :=
  evalTau precision tau2327 contact2327 logTwoBall

theorem center_sq2327 : (center2327.re : ℝ)^2 +
    (center2327.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2327]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2327 : work2327.theta.ok = true ∧
    work2327.jac.invOK = true ∧ acceptsUnitSq work2327.out = true := by
  norm_num [work2327, contact2327, tau2327, center2327, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2327 : CellCertificate where
  tauBall := tau2327
  contactCenter := center2327
  contactBall := contact2327
  work := work2327
  center_sq := center_sq2327
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2327.1
  jac_ok := checks2327.2.1
  accepted := checks2327.2.2

def cells : List CellCertificate := [cell2320, cell2321, cell2322, cell2323, cell2324, cell2325, cell2326, cell2327]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0290
