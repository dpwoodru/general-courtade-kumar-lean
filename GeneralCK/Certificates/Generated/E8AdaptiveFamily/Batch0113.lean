import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0904 : RatBall :=
  ⟨⟨-27/160, 39/160⟩, 3/320⟩
def center0904 : GaussianRat :=
  ⟨-123057717/1000000000, 167087407/1000000000⟩
def contact0904 : RatBall := localContactBall tau0904 center0904
def work0904 : RoundedTauEval :=
  evalTau precision tau0904 contact0904 logTwoBall

theorem center_sq0904 : (center0904.re : ℝ)^2 +
    (center0904.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0904]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0904 : work0904.theta.ok = true ∧
    work0904.jac.invOK = true ∧ acceptsUnitSq work0904.out = true := by
  norm_num [work0904, contact0904, tau0904, center0904, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0904 : CellCertificate where
  tauBall := tau0904
  contactCenter := center0904
  contactBall := contact0904
  work := work0904
  center_sq := center_sq0904
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0904.1
  jac_ok := checks0904.2.1
  accepted := checks0904.2.2

def tau0905 : RatBall :=
  ⟨⟨-5/32, 39/160⟩, 3/320⟩
def center0905 : GaussianRat :=
  ⟨-57074691/500000000, 83923163/500000000⟩
def contact0905 : RatBall := localContactBall tau0905 center0905
def work0905 : RoundedTauEval :=
  evalTau precision tau0905 contact0905 logTwoBall

theorem center_sq0905 : (center0905.re : ℝ)^2 +
    (center0905.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0905]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0905 : work0905.theta.ok = true ∧
    work0905.jac.invOK = true ∧ acceptsUnitSq work0905.out = true := by
  norm_num [work0905, contact0905, tau0905, center0905, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0905 : CellCertificate where
  tauBall := tau0905
  contactCenter := center0905
  contactBall := contact0905
  work := work0905
  center_sq := center_sq0905
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0905.1
  jac_ok := checks0905.2.1
  accepted := checks0905.2.2

def tau0906 : RatBall :=
  ⟨⟨-31/160, 41/160⟩, 3/320⟩
def center0906 : GaussianRat :=
  ⟨-8852011/62500000, 87111573/500000000⟩
def contact0906 : RatBall := localContactBall tau0906 center0906
def work0906 : RoundedTauEval :=
  evalTau precision tau0906 contact0906 logTwoBall

theorem center_sq0906 : (center0906.re : ℝ)^2 +
    (center0906.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0906]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0906 : work0906.theta.ok = true ∧
    work0906.jac.invOK = true ∧ acceptsUnitSq work0906.out = true := by
  norm_num [work0906, contact0906, tau0906, center0906, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0906 : CellCertificate where
  tauBall := tau0906
  contactCenter := center0906
  contactBall := contact0906
  work := work0906
  center_sq := center_sq0906
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0906.1
  jac_ok := checks0906.2.1
  accepted := checks0906.2.2

def tau0907 : RatBall :=
  ⟨⟨-29/160, 41/160⟩, 3/320⟩
def center0907 : GaussianRat :=
  ⟨-132776829/1000000000, 35027183/200000000⟩
def contact0907 : RatBall := localContactBall tau0907 center0907
def work0907 : RoundedTauEval :=
  evalTau precision tau0907 contact0907 logTwoBall

theorem center_sq0907 : (center0907.re : ℝ)^2 +
    (center0907.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0907]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0907 : work0907.theta.ok = true ∧
    work0907.jac.invOK = true ∧ acceptsUnitSq work0907.out = true := by
  norm_num [work0907, contact0907, tau0907, center0907, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0907 : CellCertificate where
  tauBall := tau0907
  contactCenter := center0907
  contactBall := contact0907
  work := work0907
  center_sq := center_sq0907
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0907.1
  jac_ok := checks0907.2.1
  accepted := checks0907.2.2

def tau0908 : RatBall :=
  ⟨⟨-31/160, 43/160⟩, 3/320⟩
def center0908 : GaussianRat :=
  ⟨-71299541/500000000, 91537843/500000000⟩
def contact0908 : RatBall := localContactBall tau0908 center0908
def work0908 : RoundedTauEval :=
  evalTau precision tau0908 contact0908 logTwoBall

theorem center_sq0908 : (center0908.re : ℝ)^2 +
    (center0908.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0908]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0908 : work0908.theta.ok = true ∧
    work0908.jac.invOK = true ∧ acceptsUnitSq work0908.out = true := by
  norm_num [work0908, contact0908, tau0908, center0908, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0908 : CellCertificate where
  tauBall := tau0908
  contactCenter := center0908
  contactBall := contact0908
  work := work0908
  center_sq := center_sq0908
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0908.1
  jac_ok := checks0908.2.1
  accepted := checks0908.2.2

def tau0909 : RatBall :=
  ⟨⟨-29/160, 43/160⟩, 3/320⟩
def center0909 : GaussianRat :=
  ⟨-66845797/500000000, 18404523/100000000⟩
def contact0909 : RatBall := localContactBall tau0909 center0909
def work0909 : RoundedTauEval :=
  evalTau precision tau0909 contact0909 logTwoBall

theorem center_sq0909 : (center0909.re : ℝ)^2 +
    (center0909.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0909]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0909 : work0909.theta.ok = true ∧
    work0909.jac.invOK = true ∧ acceptsUnitSq work0909.out = true := by
  norm_num [work0909, contact0909, tau0909, center0909, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0909 : CellCertificate where
  tauBall := tau0909
  contactCenter := center0909
  contactBall := contact0909
  work := work0909
  center_sq := center_sq0909
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0909.1
  jac_ok := checks0909.2.1
  accepted := checks0909.2.2

def tau0910 : RatBall :=
  ⟨⟨-27/160, 41/160⟩, 3/320⟩
def center0910 : GaussianRat :=
  ⟨-123867137/1000000000, 21999637/125000000⟩
def contact0910 : RatBall := localContactBall tau0910 center0910
def work0910 : RoundedTauEval :=
  evalTau precision tau0910 contact0910 logTwoBall

theorem center_sq0910 : (center0910.re : ℝ)^2 +
    (center0910.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0910]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0910 : work0910.theta.ok = true ∧
    work0910.jac.invOK = true ∧ acceptsUnitSq work0910.out = true := by
  norm_num [work0910, contact0910, tau0910, center0910, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0910 : CellCertificate where
  tauBall := tau0910
  contactCenter := center0910
  contactBall := contact0910
  work := work0910
  center_sq := center_sq0910
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0910.1
  jac_ok := checks0910.2.1
  accepted := checks0910.2.2

def tau0911 : RatBall :=
  ⟨⟨-5/32, 41/160⟩, 3/320⟩
def center0911 : GaussianRat :=
  ⟨-114906151/1000000000, 176804909/1000000000⟩
def contact0911 : RatBall := localContactBall tau0911 center0911
def work0911 : RoundedTauEval :=
  evalTau precision tau0911 contact0911 logTwoBall

theorem center_sq0911 : (center0911.re : ℝ)^2 +
    (center0911.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0911]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0911 : work0911.theta.ok = true ∧
    work0911.jac.invOK = true ∧ acceptsUnitSq work0911.out = true := by
  norm_num [work0911, contact0911, tau0911, center0911, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0911 : CellCertificate where
  tauBall := tau0911
  contactCenter := center0911
  contactBall := contact0911
  work := work0911
  center_sq := center_sq0911
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0911.1
  jac_ok := checks0911.2.1
  accepted := checks0911.2.2

def cells : List CellCertificate := [cell0904, cell0905, cell0906, cell0907, cell0908, cell0909, cell0910, cell0911]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113
