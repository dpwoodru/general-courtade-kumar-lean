import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0872 : RatBall :=
  ⟨⟨-39/160, 7/32⟩, 3/320⟩
def center0872 : GaussianRat :=
  ⟨-173384937/1000000000, 144541281/1000000000⟩
def contact0872 : RatBall := localContactBall tau0872 center0872
def work0872 : RoundedTauEval :=
  evalTau precision tau0872 contact0872 logTwoBall

theorem center_sq0872 : (center0872.re : ℝ)^2 +
    (center0872.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0872]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0872 : work0872.theta.ok = true ∧
    work0872.jac.invOK = true ∧ acceptsUnitSq work0872.out = true := by
  norm_num [work0872, contact0872, tau0872, center0872, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0872 : CellCertificate where
  tauBall := tau0872
  contactCenter := center0872
  contactBall := contact0872
  work := work0872
  center_sq := center_sq0872
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0872.1
  jac_ok := checks0872.2.1
  accepted := checks0872.2.2

def tau0873 : RatBall :=
  ⟨⟨-37/160, 7/32⟩, 3/320⟩
def center0873 : GaussianRat :=
  ⟨-164892819/1000000000, 29090197/200000000⟩
def contact0873 : RatBall := localContactBall tau0873 center0873
def work0873 : RoundedTauEval :=
  evalTau precision tau0873 contact0873 logTwoBall

theorem center_sq0873 : (center0873.re : ℝ)^2 +
    (center0873.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0873]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0873 : work0873.theta.ok = true ∧
    work0873.jac.invOK = true ∧ acceptsUnitSq work0873.out = true := by
  norm_num [work0873, contact0873, tau0873, center0873, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0873 : CellCertificate where
  tauBall := tau0873
  contactCenter := center0873
  contactBall := contact0873
  work := work0873
  center_sq := center_sq0873
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0873.1
  jac_ok := checks0873.2.1
  accepted := checks0873.2.2

def tau0874 : RatBall :=
  ⟨⟨-7/32, 33/160⟩, 3/320⟩
def center0874 : GaussianRat :=
  ⟨-31103099/200000000, 137761833/1000000000⟩
def contact0874 : RatBall := localContactBall tau0874 center0874
def work0874 : RoundedTauEval :=
  evalTau precision tau0874 contact0874 logTwoBall

theorem center_sq0874 : (center0874.re : ℝ)^2 +
    (center0874.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0874]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0874 : work0874.theta.ok = true ∧
    work0874.jac.invOK = true ∧ acceptsUnitSq work0874.out = true := by
  norm_num [work0874, contact0874, tau0874, center0874, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0874 : CellCertificate where
  tauBall := tau0874
  contactCenter := center0874
  contactBall := contact0874
  work := work0874
  center_sq := center_sq0874
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0874.1
  jac_ok := checks0874.2.1
  accepted := checks0874.2.2

def tau0875 : RatBall :=
  ⟨⟨-33/160, 33/160⟩, 3/320⟩
def center0875 : GaussianRat :=
  ⟨-73472183/500000000, 69270487/500000000⟩
def contact0875 : RatBall := localContactBall tau0875 center0875
def work0875 : RoundedTauEval :=
  evalTau precision tau0875 contact0875 logTwoBall

theorem center_sq0875 : (center0875.re : ℝ)^2 +
    (center0875.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0875]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0875 : work0875.theta.ok = true ∧
    work0875.jac.invOK = true ∧ acceptsUnitSq work0875.out = true := by
  norm_num [work0875, contact0875, tau0875, center0875, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0875 : CellCertificate where
  tauBall := tau0875
  contactCenter := center0875
  contactBall := contact0875
  work := work0875
  center_sq := center_sq0875
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0875.1
  jac_ok := checks0875.2.1
  accepted := checks0875.2.2

def tau0876 : RatBall :=
  ⟨⟨-7/32, 7/32⟩, 3/320⟩
def center0876 : GaussianRat :=
  ⟨-78170517/500000000, 14632387/100000000⟩
def contact0876 : RatBall := localContactBall tau0876 center0876
def work0876 : RoundedTauEval :=
  evalTau precision tau0876 contact0876 logTwoBall

theorem center_sq0876 : (center0876.re : ℝ)^2 +
    (center0876.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0876]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0876 : work0876.theta.ok = true ∧
    work0876.jac.invOK = true ∧ acceptsUnitSq work0876.out = true := by
  norm_num [work0876, contact0876, tau0876, center0876, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0876 : CellCertificate where
  tauBall := tau0876
  contactCenter := center0876
  contactBall := contact0876
  work := work0876
  center_sq := center_sq0876
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0876.1
  jac_ok := checks0876.2.1
  accepted := checks0876.2.2

def tau0877 : RatBall :=
  ⟨⟨-33/160, 7/32⟩, 3/320⟩
def center0877 : GaussianRat :=
  ⟨-7386597/50000000, 7357917/50000000⟩
def contact0877 : RatBall := localContactBall tau0877 center0877
def work0877 : RoundedTauEval :=
  evalTau precision tau0877 contact0877 logTwoBall

theorem center_sq0877 : (center0877.re : ℝ)^2 +
    (center0877.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0877]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0877 : work0877.theta.ok = true ∧
    work0877.jac.invOK = true ∧ acceptsUnitSq work0877.out = true := by
  norm_num [work0877, contact0877, tau0877, center0877, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0877 : CellCertificate where
  tauBall := tau0877
  contactCenter := center0877
  contactBall := contact0877
  work := work0877
  center_sq := center_sq0877
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0877.1
  jac_ok := checks0877.2.1
  accepted := checks0877.2.2

def tau0878 : RatBall :=
  ⟨⟨-39/160, 37/160⟩, 3/320⟩
def center0878 : GaussianRat :=
  ⟨-174343743/1000000000, 153020771/1000000000⟩
def contact0878 : RatBall := localContactBall tau0878 center0878
def work0878 : RoundedTauEval :=
  evalTau precision tau0878 contact0878 logTwoBall

theorem center_sq0878 : (center0878.re : ℝ)^2 +
    (center0878.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0878]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0878 : work0878.theta.ok = true ∧
    work0878.jac.invOK = true ∧ acceptsUnitSq work0878.out = true := by
  norm_num [work0878, contact0878, tau0878, center0878, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0878 : CellCertificate where
  tauBall := tau0878
  contactCenter := center0878
  contactBall := contact0878
  work := work0878
  center_sq := center_sq0878
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0878.1
  jac_ok := checks0878.2.1
  accepted := checks0878.2.2

def tau0879 : RatBall :=
  ⟨⟨-37/160, 37/160⟩, 3/320⟩
def center0879 : GaussianRat :=
  ⟨-33162899/200000000, 153992113/1000000000⟩
def contact0879 : RatBall := localContactBall tau0879 center0879
def work0879 : RoundedTauEval :=
  evalTau precision tau0879 contact0879 logTwoBall

theorem center_sq0879 : (center0879.re : ℝ)^2 +
    (center0879.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0879]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0879 : work0879.theta.ok = true ∧
    work0879.jac.invOK = true ∧ acceptsUnitSq work0879.out = true := by
  norm_num [work0879, contact0879, tau0879, center0879, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0879 : CellCertificate where
  tauBall := tau0879
  contactCenter := center0879
  contactBall := contact0879
  work := work0879
  center_sq := center_sq0879
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0879.1
  jac_ok := checks0879.2.1
  accepted := checks0879.2.2

def cells : List CellCertificate := [cell0872, cell0873, cell0874, cell0875, cell0876, cell0877, cell0878, cell0879]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109
