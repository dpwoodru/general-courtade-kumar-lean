import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0040 : RatBall :=
  ⟨⟨3/40, 1/40⟩, 3/80⟩
def center0040 : GaussianRat :=
  ⟨51918459/1000000000, 861577/50000000⟩
def contact0040 : RatBall := localContactBall tau0040 center0040
def work0040 : RoundedTauEval :=
  evalTau precision tau0040 contact0040 logTwoBall

theorem center_sq0040 : (center0040.re : ℝ)^2 +
    (center0040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0040 : work0040.theta.ok = true ∧
    work0040.jac.invOK = true ∧ acceptsUnitSq work0040.out = true := by
  norm_num [work0040, contact0040, tau0040, center0040, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0040 : CellCertificate where
  tauBall := tau0040
  contactCenter := center0040
  contactBall := contact0040
  work := work0040
  center_sq := center_sq0040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0040.1
  jac_ok := checks0040.2.1
  accepted := checks0040.2.2

def tau0041 : RatBall :=
  ⟨⟨1/40, 3/40⟩, 3/80⟩
def center0041 : GaussianRat :=
  ⟨2178341/125000000, 3253349/62500000⟩
def contact0041 : RatBall := localContactBall tau0041 center0041
def work0041 : RoundedTauEval :=
  evalTau precision tau0041 contact0041 logTwoBall

theorem center_sq0041 : (center0041.re : ℝ)^2 +
    (center0041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0041 : work0041.theta.ok = true ∧
    work0041.jac.invOK = true ∧ acceptsUnitSq work0041.out = true := by
  norm_num [work0041, contact0041, tau0041, center0041, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0041 : CellCertificate where
  tauBall := tau0041
  contactCenter := center0041
  contactBall := contact0041
  work := work0041
  center_sq := center_sq0041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0041.1
  jac_ok := checks0041.2.1
  accepted := checks0041.2.2

def tau0042 : RatBall :=
  ⟨⟨3/40, 3/40⟩, 3/80⟩
def center0042 : GaussianRat :=
  ⟨1304683/25000000, 51781961/1000000000⟩
def contact0042 : RatBall := localContactBall tau0042 center0042
def work0042 : RoundedTauEval :=
  evalTau precision tau0042 contact0042 logTwoBall

theorem center_sq0042 : (center0042.re : ℝ)^2 +
    (center0042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0042 : work0042.theta.ok = true ∧
    work0042.jac.invOK = true ∧ acceptsUnitSq work0042.out = true := by
  norm_num [work0042, contact0042, tau0042, center0042, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0042 : CellCertificate where
  tauBall := tau0042
  contactCenter := center0042
  contactBall := contact0042
  work := work0042
  center_sq := center_sq0042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0042.1
  jac_ok := checks0042.2.1
  accepted := checks0042.2.2

def tau0043 : RatBall :=
  ⟨⟨1/8, 1/40⟩, 3/80⟩
def center0043 : GaussianRat :=
  ⟨8623323/100000000, 17054997/1000000000⟩
def contact0043 : RatBall := localContactBall tau0043 center0043
def work0043 : RoundedTauEval :=
  evalTau precision tau0043 contact0043 logTwoBall

theorem center_sq0043 : (center0043.re : ℝ)^2 +
    (center0043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0043 : work0043.theta.ok = true ∧
    work0043.jac.invOK = true ∧ acceptsUnitSq work0043.out = true := by
  norm_num [work0043, contact0043, tau0043, center0043, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0043 : CellCertificate where
  tauBall := tau0043
  contactCenter := center0043
  contactBall := contact0043
  work := work0043
  center_sq := center_sq0043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0043.1
  jac_ok := checks0043.2.1
  accepted := checks0043.2.2

def tau0044 : RatBall :=
  ⟨⟨7/40, 1/40⟩, 3/80⟩
def center0044 : GaussianRat :=
  ⟨120111093/1000000000, 16796751/1000000000⟩
def contact0044 : RatBall := localContactBall tau0044 center0044
def work0044 : RoundedTauEval :=
  evalTau precision tau0044 contact0044 logTwoBall

theorem center_sq0044 : (center0044.re : ℝ)^2 +
    (center0044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0044 : work0044.theta.ok = true ∧
    work0044.jac.invOK = true ∧ acceptsUnitSq work0044.out = true := by
  norm_num [work0044, contact0044, tau0044, center0044, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0044 : CellCertificate where
  tauBall := tau0044
  contactCenter := center0044
  contactBall := contact0044
  work := work0044
  center_sq := center_sq0044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0044.1
  jac_ok := checks0044.2.1
  accepted := checks0044.2.2

def tau0045 : RatBall :=
  ⟨⟨1/8, 3/40⟩, 3/80⟩
def center0045 : GaussianRat :=
  ⟨86672281/1000000000, 1024941/20000000⟩
def contact0045 : RatBall := localContactBall tau0045 center0045
def work0045 : RoundedTauEval :=
  evalTau precision tau0045 contact0045 logTwoBall

theorem center_sq0045 : (center0045.re : ℝ)^2 +
    (center0045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0045 : work0045.theta.ok = true ∧
    work0045.jac.invOK = true ∧ acceptsUnitSq work0045.out = true := by
  norm_num [work0045, contact0045, tau0045, center0045, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0045 : CellCertificate where
  tauBall := tau0045
  contactCenter := center0045
  contactBall := contact0045
  work := work0045
  center_sq := center_sq0045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0045.1
  jac_ok := checks0045.2.1
  accepted := checks0045.2.2

def tau0046 : RatBall :=
  ⟨⟨7/40, 3/40⟩, 3/80⟩
def center0046 : GaussianRat :=
  ⟨7544217/62500000, 12616221/250000000⟩
def contact0046 : RatBall := localContactBall tau0046 center0046
def work0046 : RoundedTauEval :=
  evalTau precision tau0046 contact0046 logTwoBall

theorem center_sq0046 : (center0046.re : ℝ)^2 +
    (center0046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0046 : work0046.theta.ok = true ∧
    work0046.jac.invOK = true ∧ acceptsUnitSq work0046.out = true := by
  norm_num [work0046, contact0046, tau0046, center0046, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0046 : CellCertificate where
  tauBall := tau0046
  contactCenter := center0046
  contactBall := contact0046
  work := work0046
  center_sq := center_sq0046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0046.1
  jac_ok := checks0046.2.1
  accepted := checks0046.2.2

def tau0047 : RatBall :=
  ⟨⟨1/40, 1/8⟩, 3/80⟩
def center0047 : GaussianRat :=
  ⟨17610637/1000000000, 8705903/100000000⟩
def contact0047 : RatBall := localContactBall tau0047 center0047
def work0047 : RoundedTauEval :=
  evalTau precision tau0047 contact0047 logTwoBall

theorem center_sq0047 : (center0047.re : ℝ)^2 +
    (center0047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0047 : work0047.theta.ok = true ∧
    work0047.jac.invOK = true ∧ acceptsUnitSq work0047.out = true := by
  norm_num [work0047, contact0047, tau0047, center0047, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0047 : CellCertificate where
  tauBall := tau0047
  contactCenter := center0047
  contactBall := contact0047
  work := work0047
  center_sq := center_sq0047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0047.1
  jac_ok := checks0047.2.1
  accepted := checks0047.2.2

def cells : List CellCertificate := [cell0040, cell0041, cell0042, cell0043, cell0044, cell0045, cell0046, cell0047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005
