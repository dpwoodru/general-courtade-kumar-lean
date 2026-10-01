import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0241

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1928 : RatBall :=
  ⟨⟨-89/320, 87/320⟩, 3/640⟩
def center1928 : GaussianRat :=
  ⟨-201371579/1000000000, 177367859/1000000000⟩
def contact1928 : RatBall := localContactBall tau1928 center1928
def work1928 : RoundedTauEval :=
  evalTau precision tau1928 contact1928 logTwoBall

theorem center_sq1928 : (center1928.re : ℝ)^2 +
    (center1928.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1928]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1928 : work1928.theta.ok = true ∧
    work1928.jac.invOK = true ∧ acceptsUnitSq work1928.out = true := by
  norm_num [work1928, contact1928, tau1928, center1928, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1928 : CellCertificate where
  tauBall := tau1928
  contactCenter := center1928
  contactBall := contact1928
  work := work1928
  center_sq := center_sq1928
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1928.1
  jac_ok := checks1928.2.1
  accepted := checks1928.2.2

def tau1929 : RatBall :=
  ⟨⟨-87/320, 17/64⟩, 3/640⟩
def center1929 : GaussianRat :=
  ⟨-98252729/500000000, 34758949/200000000⟩
def contact1929 : RatBall := localContactBall tau1929 center1929
def work1929 : RoundedTauEval :=
  evalTau precision tau1929 contact1929 logTwoBall

theorem center_sq1929 : (center1929.re : ℝ)^2 +
    (center1929.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1929]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1929 : work1929.theta.ok = true ∧
    work1929.jac.invOK = true ∧ acceptsUnitSq work1929.out = true := by
  norm_num [work1929, contact1929, tau1929, center1929, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1929 : CellCertificate where
  tauBall := tau1929
  contactCenter := center1929
  contactBall := contact1929
  work := work1929
  center_sq := center_sq1929
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1929.1
  jac_ok := checks1929.2.1
  accepted := checks1929.2.2

def tau1930 : RatBall :=
  ⟨⟨-17/64, 17/64⟩, 3/640⟩
def center1930 : GaussianRat :=
  ⟨-12017011/62500000, 17442227/100000000⟩
def contact1930 : RatBall := localContactBall tau1930 center1930
def work1930 : RoundedTauEval :=
  evalTau precision tau1930 contact1930 logTwoBall

theorem center_sq1930 : (center1930.re : ℝ)^2 +
    (center1930.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1930]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1930 : work1930.theta.ok = true ∧
    work1930.jac.invOK = true ∧ acceptsUnitSq work1930.out = true := by
  norm_num [work1930, contact1930, tau1930, center1930, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1930 : CellCertificate where
  tauBall := tau1930
  contactCenter := center1930
  contactBall := contact1930
  work := work1930
  center_sq := center_sq1930
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1930.1
  jac_ok := checks1930.2.1
  accepted := checks1930.2.2

def tau1931 : RatBall :=
  ⟨⟨-87/320, 87/320⟩, 3/640⟩
def center1931 : GaussianRat :=
  ⟨-19714711/100000000, 178023711/1000000000⟩
def contact1931 : RatBall := localContactBall tau1931 center1931
def work1931 : RoundedTauEval :=
  evalTau precision tau1931 contact1931 logTwoBall

theorem center_sq1931 : (center1931.re : ℝ)^2 +
    (center1931.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1931]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1931 : work1931.theta.ok = true ∧
    work1931.jac.invOK = true ∧ acceptsUnitSq work1931.out = true := by
  norm_num [work1931, contact1931, tau1931, center1931, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1931 : CellCertificate where
  tauBall := tau1931
  contactCenter := center1931
  contactBall := contact1931
  work := work1931
  center_sq := center_sq1931
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1931.1
  jac_ok := checks1931.2.1
  accepted := checks1931.2.2

def tau1932 : RatBall :=
  ⟨⟨-17/64, 87/320⟩, 3/640⟩
def center1932 : GaussianRat :=
  ⟨-192903929/1000000000, 35733937/200000000⟩
def contact1932 : RatBall := localContactBall tau1932 center1932
def work1932 : RoundedTauEval :=
  evalTau precision tau1932 contact1932 logTwoBall

theorem center_sq1932 : (center1932.re : ℝ)^2 +
    (center1932.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1932]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1932 : work1932.theta.ok = true ∧
    work1932.jac.invOK = true ∧ acceptsUnitSq work1932.out = true := by
  norm_num [work1932, contact1932, tau1932, center1932, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1932 : CellCertificate where
  tauBall := tau1932
  contactCenter := center1932
  contactBall := contact1932
  work := work1932
  center_sq := center_sq1932
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1932.1
  jac_ok := checks1932.2.1
  accepted := checks1932.2.2

def tau1933 : RatBall :=
  ⟨⟨-83/320, 17/64⟩, 3/640⟩
def center1933 : GaussianRat :=
  ⟨-188020707/1000000000, 4375997/25000000⟩
def contact1933 : RatBall := localContactBall tau1933 center1933
def work1933 : RoundedTauEval :=
  evalTau precision tau1933 contact1933 logTwoBall

theorem center_sq1933 : (center1933.re : ℝ)^2 +
    (center1933.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1933]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1933 : work1933.theta.ok = true ∧
    work1933.jac.invOK = true ∧ acceptsUnitSq work1933.out = true := by
  norm_num [work1933, contact1933, tau1933, center1933, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1933 : CellCertificate where
  tauBall := tau1933
  contactCenter := center1933
  contactBall := contact1933
  work := work1933
  center_sq := center_sq1933
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1933.1
  jac_ok := checks1933.2.1
  accepted := checks1933.2.2

def tau1934 : RatBall :=
  ⟨⟨-81/320, 17/64⟩, 3/640⟩
def center1934 : GaussianRat :=
  ⟨-36750261/200000000, 1756473/10000000⟩
def contact1934 : RatBall := localContactBall tau1934 center1934
def work1934 : RoundedTauEval :=
  evalTau precision tau1934 contact1934 logTwoBall

theorem center_sq1934 : (center1934.re : ℝ)^2 +
    (center1934.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1934]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1934 : work1934.theta.ok = true ∧
    work1934.jac.invOK = true ∧ acceptsUnitSq work1934.out = true := by
  norm_num [work1934, contact1934, tau1934, center1934, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1934 : CellCertificate where
  tauBall := tau1934
  contactCenter := center1934
  contactBall := contact1934
  work := work1934
  center_sq := center_sq1934
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1934.1
  jac_ok := checks1934.2.1
  accepted := checks1934.2.2

def tau1935 : RatBall :=
  ⟨⟨-83/320, 87/320⟩, 3/640⟩
def center1935 : GaussianRat :=
  ⟨-188642281/1000000000, 22413187/125000000⟩
def contact1935 : RatBall := localContactBall tau1935 center1935
def work1935 : RoundedTauEval :=
  evalTau precision tau1935 contact1935 logTwoBall

theorem center_sq1935 : (center1935.re : ℝ)^2 +
    (center1935.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1935]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1935 : work1935.theta.ok = true ∧
    work1935.jac.invOK = true ∧ acceptsUnitSq work1935.out = true := by
  norm_num [work1935, contact1935, tau1935, center1935, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1935 : CellCertificate where
  tauBall := tau1935
  contactCenter := center1935
  contactBall := contact1935
  work := work1935
  center_sq := center_sq1935
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1935.1
  jac_ok := checks1935.2.1
  accepted := checks1935.2.2

def cells : List CellCertificate := [cell1928, cell1929, cell1930, cell1931, cell1932, cell1933, cell1934, cell1935]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0241
