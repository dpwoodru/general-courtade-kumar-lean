import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1864 : RatBall :=
  ⟨⟨101/320, -79/320⟩, 3/640⟩
def center1864 : GaussianRat :=
  ⟨111809453/500000000, -156912213/1000000000⟩
def contact1864 : RatBall := localContactBall tau1864 center1864
def work1864 : RoundedTauEval :=
  evalTau precision tau1864 contact1864 logTwoBall

theorem center_sq1864 : (center1864.re : ℝ)^2 +
    (center1864.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1864]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1864 : work1864.theta.ok = true ∧
    work1864.jac.invOK = true ∧ acceptsUnitSq work1864.out = true := by
  norm_num [work1864, contact1864, tau1864, center1864, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1864 : CellCertificate where
  tauBall := tau1864
  contactCenter := center1864
  contactBall := contact1864
  work := work1864
  center_sq := center_sq1864
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1864.1
  jac_ok := checks1864.2.1
  accepted := checks1864.2.2

def tau1865 : RatBall :=
  ⟨⟨101/320, -77/320⟩, 3/640⟩
def center1865 : GaussianRat :=
  ⟨111496867/500000000, -152848327/1000000000⟩
def contact1865 : RatBall := localContactBall tau1865 center1865
def work1865 : RoundedTauEval :=
  evalTau precision tau1865 contact1865 logTwoBall

theorem center_sq1865 : (center1865.re : ℝ)^2 +
    (center1865.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1865]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1865 : work1865.theta.ok = true ∧
    work1865.jac.invOK = true ∧ acceptsUnitSq work1865.out = true := by
  norm_num [work1865, contact1865, tau1865, center1865, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1865 : CellCertificate where
  tauBall := tau1865
  contactCenter := center1865
  contactBall := contact1865
  work := work1865
  center_sq := center_sq1865
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1865.1
  jac_ok := checks1865.2.1
  accepted := checks1865.2.2

def tau1866 : RatBall :=
  ⟨⟨103/320, -77/320⟩, 3/640⟩
def center1866 : GaussianRat :=
  ⟨113522317/500000000, -152229153/1000000000⟩
def contact1866 : RatBall := localContactBall tau1866 center1866
def work1866 : RoundedTauEval :=
  evalTau precision tau1866 contact1866 logTwoBall

theorem center_sq1866 : (center1866.re : ℝ)^2 +
    (center1866.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1866]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1866 : work1866.theta.ok = true ∧
    work1866.jac.invOK = true ∧ acceptsUnitSq work1866.out = true := by
  norm_num [work1866, contact1866, tau1866, center1866, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1866 : CellCertificate where
  tauBall := tau1866
  contactCenter := center1866
  contactBall := contact1866
  work := work1866
  center_sq := center_sq1866
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1866.1
  jac_ok := checks1866.2.1
  accepted := checks1866.2.2

def tau1867 : RatBall :=
  ⟨⟨101/320, -15/64⟩, 3/640⟩
def center1867 : GaussianRat :=
  ⟨13899213/62500000, -2975829/20000000⟩
def contact1867 : RatBall := localContactBall tau1867 center1867
def work1867 : RoundedTauEval :=
  evalTau precision tau1867 contact1867 logTwoBall

theorem center_sq1867 : (center1867.re : ℝ)^2 +
    (center1867.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1867]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1867 : work1867.theta.ok = true ∧
    work1867.jac.invOK = true ∧ acceptsUnitSq work1867.out = true := by
  norm_num [work1867, contact1867, tau1867, center1867, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1867 : CellCertificate where
  tauBall := tau1867
  contactCenter := center1867
  contactBall := contact1867
  work := work1867
  center_sq := center_sq1867
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1867.1
  jac_ok := checks1867.2.1
  accepted := checks1867.2.2

def tau1868 : RatBall :=
  ⟨⟨103/320, -15/64⟩, 3/640⟩
def center1868 : GaussianRat :=
  ⟨14151969/62500000, -148191091/1000000000⟩
def contact1868 : RatBall := localContactBall tau1868 center1868
def work1868 : RoundedTauEval :=
  evalTau precision tau1868 contact1868 logTwoBall

theorem center_sq1868 : (center1868.re : ℝ)^2 +
    (center1868.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1868]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1868 : work1868.theta.ok = true ∧
    work1868.jac.invOK = true ∧ acceptsUnitSq work1868.out = true := by
  norm_num [work1868, contact1868, tau1868, center1868, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1868 : CellCertificate where
  tauBall := tau1868
  contactCenter := center1868
  contactBall := contact1868
  work := work1868
  center_sq := center_sq1868
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1868.1
  jac_ok := checks1868.2.1
  accepted := checks1868.2.2

def tau1869 : RatBall :=
  ⟨⟨101/320, -73/320⟩, 3/640⟩
def center1869 : GaussianRat :=
  ⟨44359939/200000000, -72370703/500000000⟩
def contact1869 : RatBall := localContactBall tau1869 center1869
def work1869 : RoundedTauEval :=
  evalTau precision tau1869 contact1869 logTwoBall

theorem center_sq1869 : (center1869.re : ℝ)^2 +
    (center1869.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1869]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1869 : work1869.theta.ok = true ∧
    work1869.jac.invOK = true ∧ acceptsUnitSq work1869.out = true := by
  norm_num [work1869, contact1869, tau1869, center1869, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1869 : CellCertificate where
  tauBall := tau1869
  contactCenter := center1869
  contactBall := contact1869
  work := work1869
  center_sq := center_sq1869
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1869.1
  jac_ok := checks1869.2.1
  accepted := checks1869.2.2

def tau1870 : RatBall :=
  ⟨⟨103/320, -73/320⟩, 3/640⟩
def center1870 : GaussianRat :=
  ⟨5645929/25000000, -9009977/62500000⟩
def contact1870 : RatBall := localContactBall tau1870 center1870
def work1870 : RoundedTauEval :=
  evalTau precision tau1870 contact1870 logTwoBall

theorem center_sq1870 : (center1870.re : ℝ)^2 +
    (center1870.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1870]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1870 : work1870.theta.ok = true ∧
    work1870.jac.invOK = true ∧ acceptsUnitSq work1870.out = true := by
  norm_num [work1870, contact1870, tau1870, center1870, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1870 : CellCertificate where
  tauBall := tau1870
  contactCenter := center1870
  contactBall := contact1870
  work := work1870
  center_sq := center_sq1870
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1870.1
  jac_ok := checks1870.2.1
  accepted := checks1870.2.2

def tau1871 : RatBall :=
  ⟨⟨21/64, -15/64⟩, 3/640⟩
def center1871 : GaussianRat :=
  ⟨14403551/62500000, -14758413/100000000⟩
def contact1871 : RatBall := localContactBall tau1871 center1871
def work1871 : RoundedTauEval :=
  evalTau precision tau1871 contact1871 logTwoBall

theorem center_sq1871 : (center1871.re : ℝ)^2 +
    (center1871.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1871]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1871 : work1871.theta.ok = true ∧
    work1871.jac.invOK = true ∧ acceptsUnitSq work1871.out = true := by
  norm_num [work1871, contact1871, tau1871, center1871, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1871 : CellCertificate where
  tauBall := tau1871
  contactCenter := center1871
  contactBall := contact1871
  work := work1871
  center_sq := center_sq1871
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1871.1
  jac_ok := checks1871.2.1
  accepted := checks1871.2.2

def cells : List CellCertificate := [cell1864, cell1865, cell1866, cell1867, cell1868, cell1869, cell1870, cell1871]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233
