import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1912 : RatBall :=
  ⟨⟨-93/320, 79/320⟩, 3/640⟩
def center1912 : GaussianRat :=
  ⟨-207198371/1000000000, 15939079/100000000⟩
def contact1912 : RatBall := localContactBall tau1912 center1912
def work1912 : RoundedTauEval :=
  evalTau precision tau1912 contact1912 logTwoBall

theorem center_sq1912 : (center1912.re : ℝ)^2 +
    (center1912.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1912]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1912 : work1912.theta.ok = true ∧
    work1912.jac.invOK = true ∧ acceptsUnitSq work1912.out = true := by
  norm_num [work1912, contact1912, tau1912, center1912, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1912 : CellCertificate where
  tauBall := tau1912
  contactCenter := center1912
  contactBall := contact1912
  work := work1912
  center_sq := center_sq1912
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1912.1
  jac_ok := checks1912.2.1
  accepted := checks1912.2.2

def tau1913 : RatBall :=
  ⟨⟨-19/64, 81/320⟩, 3/640⟩
def center1913 : GaussianRat :=
  ⟨-211952789/1000000000, 162910673/1000000000⟩
def contact1913 : RatBall := localContactBall tau1913 center1913
def work1913 : RoundedTauEval :=
  evalTau precision tau1913 contact1913 logTwoBall

theorem center_sq1913 : (center1913.re : ℝ)^2 +
    (center1913.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1913]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1913 : work1913.theta.ok = true ∧
    work1913.jac.invOK = true ∧ acceptsUnitSq work1913.out = true := by
  norm_num [work1913, contact1913, tau1913, center1913, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1913 : CellCertificate where
  tauBall := tau1913
  contactCenter := center1913
  contactBall := contact1913
  work := work1913
  center_sq := center_sq1913
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1913.1
  jac_ok := checks1913.2.1
  accepted := checks1913.2.2

def tau1914 : RatBall :=
  ⟨⟨-93/320, 81/320⟩, 3/640⟩
def center1914 : GaussianRat :=
  ⟨-103905761/500000000, 163537217/1000000000⟩
def contact1914 : RatBall := localContactBall tau1914 center1914
def work1914 : RoundedTauEval :=
  evalTau precision tau1914 contact1914 logTwoBall

theorem center_sq1914 : (center1914.re : ℝ)^2 +
    (center1914.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1914]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1914 : work1914.theta.ok = true ∧
    work1914.jac.invOK = true ∧ acceptsUnitSq work1914.out = true := by
  norm_num [work1914, contact1914, tau1914, center1914, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1914 : CellCertificate where
  tauBall := tau1914
  contactCenter := center1914
  contactBall := contact1914
  work := work1914
  center_sq := center_sq1914
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1914.1
  jac_ok := checks1914.2.1
  accepted := checks1914.2.2

def tau1915 : RatBall :=
  ⟨⟨-19/64, 83/320⟩, 3/640⟩
def center1915 : GaussianRat :=
  ⟨-212592873/1000000000, 33409337/200000000⟩
def contact1915 : RatBall := localContactBall tau1915 center1915
def work1915 : RoundedTauEval :=
  evalTau precision tau1915 contact1915 logTwoBall

theorem center_sq1915 : (center1915.re : ℝ)^2 +
    (center1915.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1915]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1915 : work1915.theta.ok = true ∧
    work1915.jac.invOK = true ∧ acceptsUnitSq work1915.out = true := by
  norm_num [work1915, contact1915, tau1915, center1915, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1915 : CellCertificate where
  tauBall := tau1915
  contactCenter := center1915
  contactBall := contact1915
  work := work1915
  center_sq := center_sq1915
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1915.1
  jac_ok := checks1915.2.1
  accepted := checks1915.2.2

def tau1916 : RatBall :=
  ⟨⟨-93/320, 83/320⟩, 3/640⟩
def center1916 : GaussianRat :=
  ⟨-52110811/250000000, 167692033/1000000000⟩
def contact1916 : RatBall := localContactBall tau1916 center1916
def work1916 : RoundedTauEval :=
  evalTau precision tau1916 contact1916 logTwoBall

theorem center_sq1916 : (center1916.re : ℝ)^2 +
    (center1916.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1916]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1916 : work1916.theta.ok = true ∧
    work1916.jac.invOK = true ∧ acceptsUnitSq work1916.out = true := by
  norm_num [work1916, contact1916, tau1916, center1916, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1916 : CellCertificate where
  tauBall := tau1916
  contactCenter := center1916
  contactBall := contact1916
  work := work1916
  center_sq := center_sq1916
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1916.1
  jac_ok := checks1916.2.1
  accepted := checks1916.2.2

def tau1917 : RatBall :=
  ⟨⟨-91/320, 81/320⟩, 3/640⟩
def center1917 : GaussianRat :=
  ⟨-101825843/500000000, 82077687/500000000⟩
def contact1917 : RatBall := localContactBall tau1917 center1917
def work1917 : RoundedTauEval :=
  evalTau precision tau1917 contact1917 logTwoBall

theorem center_sq1917 : (center1917.re : ℝ)^2 +
    (center1917.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1917]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1917 : work1917.theta.ok = true ∧
    work1917.jac.invOK = true ∧ acceptsUnitSq work1917.out = true := by
  norm_num [work1917, contact1917, tau1917, center1917, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1917 : CellCertificate where
  tauBall := tau1917
  contactCenter := center1917
  contactBall := contact1917
  work := work1917
  center_sq := center_sq1917
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1917.1
  jac_ok := checks1917.2.1
  accepted := checks1917.2.2

def tau1918 : RatBall :=
  ⟨⟨-89/320, 81/320⟩, 3/640⟩
def center1918 : GaussianRat :=
  ⟨-199473497/1000000000, 41191221/250000000⟩
def contact1918 : RatBall := localContactBall tau1918 center1918
def work1918 : RoundedTauEval :=
  evalTau precision tau1918 contact1918 logTwoBall

theorem center_sq1918 : (center1918.re : ℝ)^2 +
    (center1918.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1918]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1918 : work1918.theta.ok = true ∧
    work1918.jac.invOK = true ∧ acceptsUnitSq work1918.out = true := by
  norm_num [work1918, contact1918, tau1918, center1918, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1918 : CellCertificate where
  tauBall := tau1918
  contactCenter := center1918
  contactBall := contact1918
  work := work1918
  center_sq := center_sq1918
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1918.1
  jac_ok := checks1918.2.1
  accepted := checks1918.2.2

def tau1919 : RatBall :=
  ⟨⟨-91/320, 83/320⟩, 3/640⟩
def center1919 : GaussianRat :=
  ⟨-204274783/1000000000, 168328783/1000000000⟩
def contact1919 : RatBall := localContactBall tau1919 center1919
def work1919 : RoundedTauEval :=
  evalTau precision tau1919 contact1919 logTwoBall

theorem center_sq1919 : (center1919.re : ℝ)^2 +
    (center1919.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1919]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1919 : work1919.theta.ok = true ∧
    work1919.jac.invOK = true ∧ acceptsUnitSq work1919.out = true := by
  norm_num [work1919, contact1919, tau1919, center1919, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1919 : CellCertificate where
  tauBall := tau1919
  contactCenter := center1919
  contactBall := contact1919
  work := work1919
  center_sq := center_sq1919
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1919.1
  jac_ok := checks1919.2.1
  accepted := checks1919.2.2

def cells : List CellCertificate := [cell1912, cell1913, cell1914, cell1915, cell1916, cell1917, cell1918, cell1919]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239
