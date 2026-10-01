import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1944 : RatBall :=
  ⟨⟨-17/64, 89/320⟩, 3/640⟩
def center1944 : GaussianRat :=
  ⟨-24194269/125000000, 5716477/31250000⟩
def contact1944 : RatBall := localContactBall tau1944 center1944
def work1944 : RoundedTauEval :=
  evalTau precision tau1944 contact1944 logTwoBall

theorem center_sq1944 : (center1944.re : ℝ)^2 +
    (center1944.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1944]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1944 : work1944.theta.ok = true ∧
    work1944.jac.invOK = true ∧ acceptsUnitSq work1944.out = true := by
  norm_num [work1944, contact1944, tau1944, center1944, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1944 : CellCertificate where
  tauBall := tau1944
  contactCenter := center1944
  contactBall := contact1944
  work := work1944
  center_sq := center_sq1944
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1944.1
  jac_ok := checks1944.2.1
  accepted := checks1944.2.2

def tau1945 : RatBall :=
  ⟨⟨-87/320, 91/320⟩, 3/640⟩
def center1945 : GaussianRat :=
  ⟨-49621711/250000000, 186511513/1000000000⟩
def contact1945 : RatBall := localContactBall tau1945 center1945
def work1945 : RoundedTauEval :=
  evalTau precision tau1945 contact1945 logTwoBall

theorem center_sq1945 : (center1945.re : ℝ)^2 +
    (center1945.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1945]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1945 : work1945.theta.ok = true ∧
    work1945.jac.invOK = true ∧ acceptsUnitSq work1945.out = true := by
  norm_num [work1945, contact1945, tau1945, center1945, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1945 : CellCertificate where
  tauBall := tau1945
  contactCenter := center1945
  contactBall := contact1945
  work := work1945
  center_sq := center_sq1945
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1945.1
  jac_ok := checks1945.2.1
  accepted := checks1945.2.2

def tau1946 : RatBall :=
  ⟨⟨-17/64, 91/320⟩, 3/640⟩
def center1946 : GaussianRat :=
  ⟨-97111567/500000000, 37439051/200000000⟩
def contact1946 : RatBall := localContactBall tau1946 center1946
def work1946 : RoundedTauEval :=
  evalTau precision tau1946 contact1946 logTwoBall

theorem center_sq1946 : (center1946.re : ℝ)^2 +
    (center1946.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1946]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1946 : work1946.theta.ok = true ∧
    work1946.jac.invOK = true ∧ acceptsUnitSq work1946.out = true := by
  norm_num [work1946, contact1946, tau1946, center1946, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1946 : CellCertificate where
  tauBall := tau1946
  contactCenter := center1946
  contactBall := contact1946
  work := work1946
  center_sq := center_sq1946
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1946.1
  jac_ok := checks1946.2.1
  accepted := checks1946.2.2

def tau1947 : RatBall :=
  ⟨⟨-83/320, 89/320⟩, 3/640⟩
def center1947 : GaussianRat :=
  ⟨-189282071/1000000000, 183581561/1000000000⟩
def contact1947 : RatBall := localContactBall tau1947 center1947
def work1947 : RoundedTauEval :=
  evalTau precision tau1947 contact1947 logTwoBall

theorem center_sq1947 : (center1947.re : ℝ)^2 +
    (center1947.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1947]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1947 : work1947.theta.ok = true ∧
    work1947.jac.invOK = true ∧ acceptsUnitSq work1947.out = true := by
  norm_num [work1947, contact1947, tau1947, center1947, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1947 : CellCertificate where
  tauBall := tau1947
  contactCenter := center1947
  contactBall := contact1947
  work := work1947
  center_sq := center_sq1947
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1947.1
  jac_ok := checks1947.2.1
  accepted := checks1947.2.2

def tau1948 : RatBall :=
  ⟨⟨-81/320, 89/320⟩, 3/640⟩
def center1948 : GaussianRat :=
  ⟨-92495743/500000000, 184225151/1000000000⟩
def contact1948 : RatBall := localContactBall tau1948 center1948
def work1948 : RoundedTauEval :=
  evalTau precision tau1948 contact1948 logTwoBall

theorem center_sq1948 : (center1948.re : ℝ)^2 +
    (center1948.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1948]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1948 : work1948.theta.ok = true ∧
    work1948.jac.invOK = true ∧ acceptsUnitSq work1948.out = true := by
  norm_num [work1948, contact1948, tau1948, center1948, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1948 : CellCertificate where
  tauBall := tau1948
  contactCenter := center1948
  contactBall := contact1948
  work := work1948
  center_sq := center_sq1948
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1948.1
  jac_ok := checks1948.2.1
  accepted := checks1948.2.2

def tau1949 : RatBall :=
  ⟨⟨-83/320, 91/320⟩, 3/640⟩
def center1949 : GaussianRat :=
  ⟨-37988073/200000000, 37573667/200000000⟩
def contact1949 : RatBall := localContactBall tau1949 center1949
def work1949 : RoundedTauEval :=
  evalTau precision tau1949 contact1949 logTwoBall

theorem center_sq1949 : (center1949.re : ℝ)^2 +
    (center1949.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1949]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1949 : work1949.theta.ok = true ∧
    work1949.jac.invOK = true ∧ acceptsUnitSq work1949.out = true := by
  norm_num [work1949, contact1949, tau1949, center1949, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1949 : CellCertificate where
  tauBall := tau1949
  contactCenter := center1949
  contactBall := contact1949
  work := work1949
  center_sq := center_sq1949
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1949.1
  jac_ok := checks1949.2.1
  accepted := checks1949.2.2

def tau1950 : RatBall :=
  ⟨⟨-81/320, 91/320⟩, 3/640⟩
def center1950 : GaussianRat :=
  ⟨-23204849/125000000, 94265223/500000000⟩
def contact1950 : RatBall := localContactBall tau1950 center1950
def work1950 : RoundedTauEval :=
  evalTau precision tau1950 contact1950 logTwoBall

theorem center_sq1950 : (center1950.re : ℝ)^2 +
    (center1950.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1950]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1950 : work1950.theta.ok = true ∧
    work1950.jac.invOK = true ∧ acceptsUnitSq work1950.out = true := by
  norm_num [work1950, contact1950, tau1950, center1950, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1950 : CellCertificate where
  tauBall := tau1950
  contactCenter := center1950
  contactBall := contact1950
  work := work1950
  center_sq := center_sq1950
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1950.1
  jac_ok := checks1950.2.1
  accepted := checks1950.2.2

def tau1951 : RatBall :=
  ⟨⟨-87/320, 93/320⟩, 3/640⟩
def center1951 : GaussianRat :=
  ⟨-2489819/12500000, 47692707/250000000⟩
def contact1951 : RatBall := localContactBall tau1951 center1951
def work1951 : RoundedTauEval :=
  evalTau precision tau1951 contact1951 logTwoBall

theorem center_sq1951 : (center1951.re : ℝ)^2 +
    (center1951.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1951]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1951 : work1951.theta.ok = true ∧
    work1951.jac.invOK = true ∧ acceptsUnitSq work1951.out = true := by
  norm_num [work1951, contact1951, tau1951, center1951, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1951 : CellCertificate where
  tauBall := tau1951
  contactCenter := center1951
  contactBall := contact1951
  work := work1951
  center_sq := center_sq1951
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1951.1
  jac_ok := checks1951.2.1
  accepted := checks1951.2.2

def cells : List CellCertificate := [cell1944, cell1945, cell1946, cell1947, cell1948, cell1949, cell1950, cell1951]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243
