import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1920 : RatBall :=
  ⟨⟨-89/320, 83/320⟩, 3/640⟩
def center1920 : GaussianRat :=
  ⟨-100043853/500000000, 84478333/500000000⟩
def contact1920 : RatBall := localContactBall tau1920 center1920
def work1920 : RoundedTauEval :=
  evalTau precision tau1920 contact1920 logTwoBall

theorem center_sq1920 : (center1920.re : ℝ)^2 +
    (center1920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1920 : work1920.theta.ok = true ∧
    work1920.jac.invOK = true ∧ acceptsUnitSq work1920.out = true := by
  norm_num [work1920, contact1920, tau1920, center1920, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1920 : CellCertificate where
  tauBall := tau1920
  contactCenter := center1920
  contactBall := contact1920
  work := work1920
  center_sq := center_sq1920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1920.1
  jac_ok := checks1920.2.1
  accepted := checks1920.2.2

def tau1921 : RatBall :=
  ⟨⟨-19/64, 17/64⟩, 3/640⟩
def center1921 : GaussianRat :=
  ⟨-42650399/200000000, 171191029/1000000000⟩
def contact1921 : RatBall := localContactBall tau1921 center1921
def work1921 : RoundedTauEval :=
  evalTau precision tau1921 contact1921 logTwoBall

theorem center_sq1921 : (center1921.re : ℝ)^2 +
    (center1921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1921 : work1921.theta.ok = true ∧
    work1921.jac.invOK = true ∧ acceptsUnitSq work1921.out = true := by
  norm_num [work1921, contact1921, tau1921, center1921, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1921 : CellCertificate where
  tauBall := tau1921
  contactCenter := center1921
  contactBall := contact1921
  work := work1921
  center_sq := center_sq1921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1921.1
  jac_ok := checks1921.2.1
  accepted := checks1921.2.2

def tau1922 : RatBall :=
  ⟨⟨-93/320, 17/64⟩, 3/640⟩
def center1922 : GaussianRat :=
  ⟨-104546899/500000000, 171855447/1000000000⟩
def contact1922 : RatBall := localContactBall tau1922 center1922
def work1922 : RoundedTauEval :=
  evalTau precision tau1922 contact1922 logTwoBall

theorem center_sq1922 : (center1922.re : ℝ)^2 +
    (center1922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1922 : work1922.theta.ok = true ∧
    work1922.jac.invOK = true ∧ acceptsUnitSq work1922.out = true := by
  norm_num [work1922, contact1922, tau1922, center1922, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1922 : CellCertificate where
  tauBall := tau1922
  contactCenter := center1922
  contactBall := contact1922
  work := work1922
  center_sq := center_sq1922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1922.1
  jac_ok := checks1922.2.1
  accepted := checks1922.2.2

def tau1923 : RatBall :=
  ⟨⟨-19/64, 87/320⟩, 3/640⟩
def center1923 : GaussianRat :=
  ⟨-106965213/500000000, 35068781/200000000⟩
def contact1923 : RatBall := localContactBall tau1923 center1923
def work1923 : RoundedTauEval :=
  evalTau precision tau1923 contact1923 logTwoBall

theorem center_sq1923 : (center1923.re : ℝ)^2 +
    (center1923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1923 : work1923.theta.ok = true ∧
    work1923.jac.invOK = true ∧ acceptsUnitSq work1923.out = true := by
  norm_num [work1923, contact1923, tau1923, center1923, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1923 : CellCertificate where
  tauBall := tau1923
  contactCenter := center1923
  contactBall := contact1923
  work := work1923
  center_sq := center_sq1923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1923.1
  jac_ok := checks1923.2.1
  accepted := checks1923.2.2

def tau1924 : RatBall :=
  ⟨⟨-93/320, 87/320⟩, 3/640⟩
def center1924 : GaussianRat :=
  ⟨-1638777/7812500, 17602767/100000000⟩
def contact1924 : RatBall := localContactBall tau1924 center1924
def work1924 : RoundedTauEval :=
  evalTau precision tau1924 contact1924 logTwoBall

theorem center_sq1924 : (center1924.re : ℝ)^2 +
    (center1924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1924 : work1924.theta.ok = true ∧
    work1924.jac.invOK = true ∧ acceptsUnitSq work1924.out = true := by
  norm_num [work1924, contact1924, tau1924, center1924, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1924 : CellCertificate where
  tauBall := tau1924
  contactCenter := center1924
  contactBall := contact1924
  work := work1924
  center_sq := center_sq1924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1924.1
  jac_ok := checks1924.2.1
  accepted := checks1924.2.2

def tau1925 : RatBall :=
  ⟨⟨-91/320, 17/64⟩, 3/640⟩
def center1925 : GaussianRat :=
  ⟨-102458249/500000000, 172511057/1000000000⟩
def contact1925 : RatBall := localContactBall tau1925 center1925
def work1925 : RoundedTauEval :=
  evalTau precision tau1925 contact1925 logTwoBall

theorem center_sq1925 : (center1925.re : ℝ)^2 +
    (center1925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1925 : work1925.theta.ok = true ∧
    work1925.jac.invOK = true ∧ acceptsUnitSq work1925.out = true := by
  norm_num [work1925, contact1925, tau1925, center1925, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1925 : CellCertificate where
  tauBall := tau1925
  contactCenter := center1925
  contactBall := contact1925
  work := work1925
  center_sq := center_sq1925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1925.1
  jac_ok := checks1925.2.1
  accepted := checks1925.2.2

def tau1926 : RatBall :=
  ⟨⟨-89/320, 17/64⟩, 3/640⟩
def center1926 : GaussianRat :=
  ⟨-20072031/100000000, 86578791/500000000⟩
def contact1926 : RatBall := localContactBall tau1926 center1926
def work1926 : RoundedTauEval :=
  evalTau precision tau1926 contact1926 logTwoBall

theorem center_sq1926 : (center1926.re : ℝ)^2 +
    (center1926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1926 : work1926.theta.ok = true ∧
    work1926.jac.invOK = true ∧ acceptsUnitSq work1926.out = true := by
  norm_num [work1926, contact1926, tau1926, center1926, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1926 : CellCertificate where
  tauBall := tau1926
  contactCenter := center1926
  contactBall := contact1926
  work := work1926
  center_sq := center_sq1926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1926.1
  jac_ok := checks1926.2.1
  accepted := checks1926.2.2

def tau1927 : RatBall :=
  ⟨⟨-91/320, 87/320⟩, 3/640⟩
def center1927 : GaussianRat :=
  ⟨-102788551/500000000, 176702417/1000000000⟩
def contact1927 : RatBall := localContactBall tau1927 center1927
def work1927 : RoundedTauEval :=
  evalTau precision tau1927 contact1927 logTwoBall

theorem center_sq1927 : (center1927.re : ℝ)^2 +
    (center1927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1927]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1927 : work1927.theta.ok = true ∧
    work1927.jac.invOK = true ∧ acceptsUnitSq work1927.out = true := by
  norm_num [work1927, contact1927, tau1927, center1927, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1927 : CellCertificate where
  tauBall := tau1927
  contactCenter := center1927
  contactBall := contact1927
  work := work1927
  center_sq := center_sq1927
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1927.1
  jac_ok := checks1927.2.1
  accepted := checks1927.2.2

def cells : List CellCertificate := [cell1920, cell1921, cell1922, cell1923, cell1924, cell1925, cell1926, cell1927]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240
