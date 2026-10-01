import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0292

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2336 : RatBall :=
  ⟨⟨41/320, 109/320⟩, 3/640⟩
def center2336 : GaussianRat :=
  ⟨6249053/62500000, 241270351/1000000000⟩
def contact2336 : RatBall := localContactBall tau2336 center2336
def work2336 : RoundedTauEval :=
  evalTau precision tau2336 contact2336 logTwoBall

theorem center_sq2336 : (center2336.re : ℝ)^2 +
    (center2336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2336 : work2336.theta.ok = true ∧
    work2336.jac.invOK = true ∧ acceptsUnitSq work2336.out = true := by
  norm_num [work2336, contact2336, tau2336, center2336, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2336 : CellCertificate where
  tauBall := tau2336
  contactCenter := center2336
  contactBall := contact2336
  work := work2336
  center_sq := center_sq2336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2336.1
  jac_ok := checks2336.2.1
  accepted := checks2336.2.2

def tau2337 : RatBall :=
  ⟨⟨43/320, 109/320⟩, 3/640⟩
def center2337 : GaussianRat :=
  ⟨26190451/250000000, 3762143/15625000⟩
def contact2337 : RatBall := localContactBall tau2337 center2337
def work2337 : RoundedTauEval :=
  evalTau precision tau2337 contact2337 logTwoBall

theorem center_sq2337 : (center2337.re : ℝ)^2 +
    (center2337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2337 : work2337.theta.ok = true ∧
    work2337.jac.invOK = true ∧ acceptsUnitSq work2337.out = true := by
  norm_num [work2337, contact2337, tau2337, center2337, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2337 : CellCertificate where
  tauBall := tau2337
  contactCenter := center2337
  contactBall := contact2337
  work := work2337
  center_sq := center_sq2337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2337.1
  jac_ok := checks2337.2.1
  accepted := checks2337.2.2

def tau2338 : RatBall :=
  ⟨⟨41/320, 111/320⟩, 3/640⟩
def center2338 : GaussianRat :=
  ⟨100474143/1000000000, 123032409/500000000⟩
def contact2338 : RatBall := localContactBall tau2338 center2338
def work2338 : RoundedTauEval :=
  evalTau precision tau2338 contact2338 logTwoBall

theorem center_sq2338 : (center2338.re : ℝ)^2 +
    (center2338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2338 : work2338.theta.ok = true ∧
    work2338.jac.invOK = true ∧ acceptsUnitSq work2338.out = true := by
  norm_num [work2338, contact2338, tau2338, center2338, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2338 : CellCertificate where
  tauBall := tau2338
  contactCenter := center2338
  contactBall := contact2338
  work := work2338
  center_sq := center_sq2338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2338.1
  jac_ok := checks2338.2.1
  accepted := checks2338.2.2

def tau2339 : RatBall :=
  ⟨⟨43/320, 111/320⟩, 3/640⟩
def center2339 : GaussianRat :=
  ⟨21054511/200000000, 122778933/500000000⟩
def contact2339 : RatBall := localContactBall tau2339 center2339
def work2339 : RoundedTauEval :=
  evalTau precision tau2339 contact2339 logTwoBall

theorem center_sq2339 : (center2339.re : ℝ)^2 +
    (center2339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2339 : work2339.theta.ok = true ∧
    work2339.jac.invOK = true ∧ acceptsUnitSq work2339.out = true := by
  norm_num [work2339, contact2339, tau2339, center2339, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2339 : CellCertificate where
  tauBall := tau2339
  contactCenter := center2339
  contactBall := contact2339
  work := work2339
  center_sq := center_sq2339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2339.1
  jac_ok := checks2339.2.1
  accepted := checks2339.2.2

def tau2340 : RatBall :=
  ⟨⟨9/64, 109/320⟩, 3/640⟩
def center2340 : GaussianRat :=
  ⟨109524891/1000000000, 240262931/1000000000⟩
def contact2340 : RatBall := localContactBall tau2340 center2340
def work2340 : RoundedTauEval :=
  evalTau precision tau2340 contact2340 logTwoBall

theorem center_sq2340 : (center2340.re : ℝ)^2 +
    (center2340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2340 : work2340.theta.ok = true ∧
    work2340.jac.invOK = true ∧ acceptsUnitSq work2340.out = true := by
  norm_num [work2340, contact2340, tau2340, center2340, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2340 : CellCertificate where
  tauBall := tau2340
  contactCenter := center2340
  contactBall := contact2340
  work := work2340
  center_sq := center_sq2340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2340.1
  jac_ok := checks2340.2.1
  accepted := checks2340.2.2

def tau2341 : RatBall :=
  ⟨⟨47/320, 109/320⟩, 3/640⟩
def center2341 : GaussianRat :=
  ⟨3571049/31250000, 239728011/1000000000⟩
def contact2341 : RatBall := localContactBall tau2341 center2341
def work2341 : RoundedTauEval :=
  evalTau precision tau2341 contact2341 logTwoBall

theorem center_sq2341 : (center2341.re : ℝ)^2 +
    (center2341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2341 : work2341.theta.ok = true ∧
    work2341.jac.invOK = true ∧ acceptsUnitSq work2341.out = true := by
  norm_num [work2341, contact2341, tau2341, center2341, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2341 : CellCertificate where
  tauBall := tau2341
  contactCenter := center2341
  contactBall := contact2341
  work := work2341
  center_sq := center_sq2341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2341.1
  jac_ok := checks2341.2.1
  accepted := checks2341.2.2

def tau2342 : RatBall :=
  ⟨⟨9/64, 111/320⟩, 3/640⟩
def center2342 : GaussianRat :=
  ⟨4402271/40000000, 122514671/500000000⟩
def contact2342 : RatBall := localContactBall tau2342 center2342
def work2342 : RoundedTauEval :=
  evalTau precision tau2342 contact2342 logTwoBall

theorem center_sq2342 : (center2342.re : ℝ)^2 +
    (center2342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2342 : work2342.theta.ok = true ∧
    work2342.jac.invOK = true ∧ acceptsUnitSq work2342.out = true := by
  norm_num [work2342, contact2342, tau2342, center2342, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2342 : CellCertificate where
  tauBall := tau2342
  contactCenter := center2342
  contactBall := contact2342
  work := work2342
  center_sq := center_sq2342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2342.1
  jac_ok := checks2342.2.1
  accepted := checks2342.2.2

def tau2343 : RatBall :=
  ⟨⟨47/320, 111/320⟩, 3/640⟩
def center2343 : GaussianRat :=
  ⟨57413127/500000000, 244479579/1000000000⟩
def contact2343 : RatBall := localContactBall tau2343 center2343
def work2343 : RoundedTauEval :=
  evalTau precision tau2343 contact2343 logTwoBall

theorem center_sq2343 : (center2343.re : ℝ)^2 +
    (center2343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2343 : work2343.theta.ok = true ∧
    work2343.jac.invOK = true ∧ acceptsUnitSq work2343.out = true := by
  norm_num [work2343, contact2343, tau2343, center2343, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2343 : CellCertificate where
  tauBall := tau2343
  contactCenter := center2343
  contactBall := contact2343
  work := work2343
  center_sq := center_sq2343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2343.1
  jac_ok := checks2343.2.1
  accepted := checks2343.2.2

def cells : List CellCertificate := [cell2336, cell2337, cell2338, cell2339, cell2340, cell2341, cell2342, cell2343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0292
