import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1904 : RatBall :=
  ⟨⟨-99/320, 81/320⟩, 3/640⟩
def center1904 : GaussianRat :=
  ⟨-55044701/250000000, 161633449/1000000000⟩
def contact1904 : RatBall := localContactBall tau1904 center1904
def work1904 : RoundedTauEval :=
  evalTau precision tau1904 contact1904 logTwoBall

theorem center_sq1904 : (center1904.re : ℝ)^2 +
    (center1904.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1904]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1904 : work1904.theta.ok = true ∧
    work1904.jac.invOK = true ∧ acceptsUnitSq work1904.out = true := by
  norm_num [work1904, contact1904, tau1904, center1904, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1904 : CellCertificate where
  tauBall := tau1904
  contactCenter := center1904
  contactBall := contact1904
  work := work1904
  center_sq := center_sq1904
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1904.1
  jac_ok := checks1904.2.1
  accepted := checks1904.2.2

def tau1905 : RatBall :=
  ⟨⟨-97/320, 81/320⟩, 3/640⟩
def center1905 : GaussianRat :=
  ⟨-108037641/500000000, 81137999/500000000⟩
def contact1905 : RatBall := localContactBall tau1905 center1905
def work1905 : RoundedTauEval :=
  evalTau precision tau1905 contact1905 logTwoBall

theorem center_sq1905 : (center1905.re : ℝ)^2 +
    (center1905.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1905]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1905 : work1905.theta.ok = true ∧
    work1905.jac.invOK = true ∧ acceptsUnitSq work1905.out = true := by
  norm_num [work1905, contact1905, tau1905, center1905, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1905 : CellCertificate where
  tauBall := tau1905
  contactCenter := center1905
  contactBall := contact1905
  work := work1905
  center_sq := center_sq1905
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1905.1
  jac_ok := checks1905.2.1
  accepted := checks1905.2.2

def tau1906 : RatBall :=
  ⟨⟨-99/320, 83/320⟩, 3/640⟩
def center1906 : GaussianRat :=
  ⟨-110417413/500000000, 165731261/1000000000⟩
def contact1906 : RatBall := localContactBall tau1906 center1906
def work1906 : RoundedTauEval :=
  evalTau precision tau1906 contact1906 logTwoBall

theorem center_sq1906 : (center1906.re : ℝ)^2 +
    (center1906.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1906]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1906 : work1906.theta.ok = true ∧
    work1906.jac.invOK = true ∧ acceptsUnitSq work1906.out = true := by
  norm_num [work1906, contact1906, tau1906, center1906, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1906 : CellCertificate where
  tauBall := tau1906
  contactCenter := center1906
  contactBall := contact1906
  work := work1906
  center_sq := center_sq1906
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1906.1
  jac_ok := checks1906.2.1
  accepted := checks1906.2.2

def tau1907 : RatBall :=
  ⟨⟨-97/320, 83/320⟩, 3/640⟩
def center1907 : GaussianRat :=
  ⟨-108361733/500000000, 83196503/500000000⟩
def contact1907 : RatBall := localContactBall tau1907 center1907
def work1907 : RoundedTauEval :=
  evalTau precision tau1907 contact1907 logTwoBall

theorem center_sq1907 : (center1907.re : ℝ)^2 +
    (center1907.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1907]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1907 : work1907.theta.ok = true ∧
    work1907.jac.invOK = true ∧ acceptsUnitSq work1907.out = true := by
  norm_num [work1907, contact1907, tau1907, center1907, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1907 : CellCertificate where
  tauBall := tau1907
  contactCenter := center1907
  contactBall := contact1907
  work := work1907
  center_sq := center_sq1907
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1907.1
  jac_ok := checks1907.2.1
  accepted := checks1907.2.2

def tau1908 : RatBall :=
  ⟨⟨-97/320, 17/64⟩, 3/640⟩
def center1908 : GaussianRat :=
  ⟨-54347721/250000000, 170518079/1000000000⟩
def contact1908 : RatBall := localContactBall tau1908 center1908
def work1908 : RoundedTauEval :=
  evalTau precision tau1908 contact1908 logTwoBall

theorem center_sq1908 : (center1908.re : ℝ)^2 +
    (center1908.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1908]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1908 : work1908.theta.ok = true ∧
    work1908.jac.invOK = true ∧ acceptsUnitSq work1908.out = true := by
  norm_num [work1908, contact1908, tau1908, center1908, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1908 : CellCertificate where
  tauBall := tau1908
  contactCenter := center1908
  contactBall := contact1908
  work := work1908
  center_sq := center_sq1908
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1908.1
  jac_ok := checks1908.2.1
  accepted := checks1908.2.2

def tau1909 : RatBall :=
  ⟨⟨-19/64, 77/320⟩, 3/640⟩
def center1909 : GaussianRat :=
  ⟨-26341087/125000000, 77331419/500000000⟩
def contact1909 : RatBall := localContactBall tau1909 center1909
def work1909 : RoundedTauEval :=
  evalTau precision tau1909 contact1909 logTwoBall

theorem center_sq1909 : (center1909.re : ℝ)^2 +
    (center1909.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1909]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1909 : work1909.theta.ok = true ∧
    work1909.jac.invOK = true ∧ acceptsUnitSq work1909.out = true := by
  norm_num [work1909, contact1909, tau1909, center1909, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1909 : CellCertificate where
  tauBall := tau1909
  contactCenter := center1909
  contactBall := contact1909
  work := work1909
  center_sq := center_sq1909
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1909.1
  jac_ok := checks1909.2.1
  accepted := checks1909.2.2

def tau1910 : RatBall :=
  ⟨⟨-93/320, 77/320⟩, 3/640⟩
def center1910 : GaussianRat :=
  ⟨-12912721/62500000, 7762627/50000000⟩
def contact1910 : RatBall := localContactBall tau1910 center1910
def work1910 : RoundedTauEval :=
  evalTau precision tau1910 contact1910 logTwoBall

theorem center_sq1910 : (center1910.re : ℝ)^2 +
    (center1910.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1910]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1910 : work1910.theta.ok = true ∧
    work1910.jac.invOK = true ∧ acceptsUnitSq work1910.out = true := by
  norm_num [work1910, contact1910, tau1910, center1910, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1910 : CellCertificate where
  tauBall := tau1910
  contactCenter := center1910
  contactBall := contact1910
  work := work1910
  center_sq := center_sq1910
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1910.1
  jac_ok := checks1910.2.1
  accepted := checks1910.2.2

def tau1911 : RatBall :=
  ⟨⟨-19/64, 79/320⟩, 3/640⟩
def center1911 : GaussianRat :=
  ⟨-211331481/1000000000, 158782791/1000000000⟩
def contact1911 : RatBall := localContactBall tau1911 center1911
def work1911 : RoundedTauEval :=
  evalTau precision tau1911 contact1911 logTwoBall

theorem center_sq1911 : (center1911.re : ℝ)^2 +
    (center1911.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1911]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1911 : work1911.theta.ok = true ∧
    work1911.jac.invOK = true ∧ acceptsUnitSq work1911.out = true := by
  norm_num [work1911, contact1911, tau1911, center1911, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1911 : CellCertificate where
  tauBall := tau1911
  contactCenter := center1911
  contactBall := contact1911
  work := work1911
  center_sq := center_sq1911
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1911.1
  jac_ok := checks1911.2.1
  accepted := checks1911.2.2

def cells : List CellCertificate := [cell1904, cell1905, cell1906, cell1907, cell1908, cell1909, cell1910, cell1911]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238
