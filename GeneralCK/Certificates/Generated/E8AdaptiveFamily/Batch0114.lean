import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0114

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0912 : RatBall :=
  ⟨⟨-27/160, 43/160⟩, 3/320⟩
def center0912 : GaussianRat :=
  ⟨-1948873/15625000, 92480083/500000000⟩
def contact0912 : RatBall := localContactBall tau0912 center0912
def work0912 : RoundedTauEval :=
  evalTau precision tau0912 contact0912 logTwoBall

theorem center_sq0912 : (center0912.re : ℝ)^2 +
    (center0912.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0912]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0912 : work0912.theta.ok = true ∧
    work0912.jac.invOK = true ∧ acceptsUnitSq work0912.out = true := by
  norm_num [work0912, contact0912, tau0912, center0912, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0912 : CellCertificate where
  tauBall := tau0912
  contactCenter := center0912
  contactBall := contact0912
  work := work0912
  center_sq := center_sq0912
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0912.1
  jac_ok := checks0912.2.1
  accepted := checks0912.2.2

def tau0913 : RatBall :=
  ⟨⟨-5/32, 43/160⟩, 3/320⟩
def center0913 : GaussianRat :=
  ⟨-57855523/500000000, 185818573/1000000000⟩
def contact0913 : RatBall := localContactBall tau0913 center0913
def work0913 : RoundedTauEval :=
  evalTau precision tau0913 contact0913 logTwoBall

theorem center_sq0913 : (center0913.re : ℝ)^2 +
    (center0913.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0913]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0913 : work0913.theta.ok = true ∧
    work0913.jac.invOK = true ∧ acceptsUnitSq work0913.out = true := by
  norm_num [work0913, contact0913, tau0913, center0913, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0913 : CellCertificate where
  tauBall := tau0913
  contactCenter := center0913
  contactBall := contact0913
  work := work0913
  center_sq := center_sq0913
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0913.1
  jac_ok := checks0913.2.1
  accepted := checks0913.2.2

def tau0914 : RatBall :=
  ⟨⟨-31/160, 9/32⟩, 3/320⟩
def center0914 : GaussianRat :=
  ⟨-143625227/1000000000, 38396169/200000000⟩
def contact0914 : RatBall := localContactBall tau0914 center0914
def work0914 : RoundedTauEval :=
  evalTau precision tau0914 contact0914 logTwoBall

theorem center_sq0914 : (center0914.re : ℝ)^2 +
    (center0914.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0914]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0914 : work0914.theta.ok = true ∧
    work0914.jac.invOK = true ∧ acceptsUnitSq work0914.out = true := by
  norm_num [work0914, contact0914, tau0914, center0914, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0914 : CellCertificate where
  tauBall := tau0914
  contactCenter := center0914
  contactBall := contact0914
  work := work0914
  center_sq := center_sq0914
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0914.1
  jac_ok := checks0914.2.1
  accepted := checks0914.2.2

def tau0915 : RatBall :=
  ⟨⟨-29/160, 9/32⟩, 3/320⟩
def center0915 : GaussianRat :=
  ⟨-67331309/500000000, 193009163/1000000000⟩
def contact0915 : RatBall := localContactBall tau0915 center0915
def work0915 : RoundedTauEval :=
  evalTau precision tau0915 contact0915 logTwoBall

theorem center_sq0915 : (center0915.re : ℝ)^2 +
    (center0915.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0915]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0915 : work0915.theta.ok = true ∧
    work0915.jac.invOK = true ∧ acceptsUnitSq work0915.out = true := by
  norm_num [work0915, contact0915, tau0915, center0915, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0915 : CellCertificate where
  tauBall := tau0915
  contactCenter := center0915
  contactBall := contact0915
  work := work0915
  center_sq := center_sq0915
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0915.1
  jac_ok := checks0915.2.1
  accepted := checks0915.2.2

def tau0916 : RatBall :=
  ⟨⟨-31/160, 47/160⟩, 3/320⟩
def center0916 : GaussianRat :=
  ⟨-5788509/40000000, 200941561/1000000000⟩
def contact0916 : RatBall := localContactBall tau0916 center0916
def work0916 : RoundedTauEval :=
  evalTau precision tau0916 contact0916 logTwoBall

theorem center_sq0916 : (center0916.re : ℝ)^2 +
    (center0916.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0916]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0916 : work0916.theta.ok = true ∧
    work0916.jac.invOK = true ∧ acceptsUnitSq work0916.out = true := by
  norm_num [work0916, contact0916, tau0916, center0916, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0916 : CellCertificate where
  tauBall := tau0916
  contactCenter := center0916
  contactBall := contact0916
  work := work0916
  center_sq := center_sq0916
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0916.1
  jac_ok := checks0916.2.1
  accepted := checks0916.2.2

def tau0917 : RatBall :=
  ⟨⟨-29/160, 47/160⟩, 3/320⟩
def center0917 : GaussianRat :=
  ⟨-135691941/1000000000, 202030811/1000000000⟩
def contact0917 : RatBall := localContactBall tau0917 center0917
def work0917 : RoundedTauEval :=
  evalTau precision tau0917 contact0917 logTwoBall

theorem center_sq0917 : (center0917.re : ℝ)^2 +
    (center0917.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0917]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0917 : work0917.theta.ok = true ∧
    work0917.jac.invOK = true ∧ acceptsUnitSq work0917.out = true := by
  norm_num [work0917, contact0917, tau0917, center0917, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0917 : CellCertificate where
  tauBall := tau0917
  contactCenter := center0917
  contactBall := contact0917
  work := work0917
  center_sq := center_sq0917
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0917.1
  jac_ok := checks0917.2.1
  accepted := checks0917.2.2

def tau0918 : RatBall :=
  ⟨⟨-27/160, 9/32⟩, 3/320⟩
def center0918 : GaussianRat :=
  ⟨-25128347/200000000, 9698989/50000000⟩
def contact0918 : RatBall := localContactBall tau0918 center0918
def work0918 : RoundedTauEval :=
  evalTau precision tau0918 contact0918 logTwoBall

theorem center_sq0918 : (center0918.re : ℝ)^2 +
    (center0918.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0918]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0918 : work0918.theta.ok = true ∧
    work0918.jac.invOK = true ∧ acceptsUnitSq work0918.out = true := by
  norm_num [work0918, contact0918, tau0918, center0918, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0918 : CellCertificate where
  tauBall := tau0918
  contactCenter := center0918
  contactBall := contact0918
  work := work0918
  center_sq := center_sq0918
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0918.1
  jac_ok := checks0918.2.1
  accepted := checks0918.2.2

def tau0919 : RatBall :=
  ⟨⟨-5/32, 9/32⟩, 3/320⟩
def center0919 : GaussianRat :=
  ⟨-116565793/1000000000, 194890619/1000000000⟩
def contact0919 : RatBall := localContactBall tau0919 center0919
def work0919 : RoundedTauEval :=
  evalTau precision tau0919 contact0919 logTwoBall

theorem center_sq0919 : (center0919.re : ℝ)^2 +
    (center0919.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0919]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0919 : work0919.theta.ok = true ∧
    work0919.jac.invOK = true ∧ acceptsUnitSq work0919.out = true := by
  norm_num [work0919, contact0919, tau0919, center0919, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0919 : CellCertificate where
  tauBall := tau0919
  contactCenter := center0919
  contactBall := contact0919
  work := work0919
  center_sq := center_sq0919
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0919.1
  jac_ok := checks0919.2.1
  accepted := checks0919.2.2

def cells : List CellCertificate := [cell0912, cell0913, cell0914, cell0915, cell0916, cell0917, cell0918, cell0919]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0114
