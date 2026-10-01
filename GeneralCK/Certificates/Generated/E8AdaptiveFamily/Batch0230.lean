import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0230

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1840 : RatBall :=
  ⟨⟨19/64, -87/320⟩, 3/640⟩
def center1840 : GaussianRat :=
  ⟨106965213/500000000, -35068781/200000000⟩
def contact1840 : RatBall := localContactBall tau1840 center1840
def work1840 : RoundedTauEval :=
  evalTau precision tau1840 contact1840 logTwoBall

theorem center_sq1840 : (center1840.re : ℝ)^2 +
    (center1840.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1840 : work1840.theta.ok = true ∧
    work1840.jac.invOK = true ∧ acceptsUnitSq work1840.out = true := by
  norm_num [work1840, contact1840, tau1840, center1840, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1840 : CellCertificate where
  tauBall := tau1840
  contactCenter := center1840
  contactBall := contact1840
  work := work1840
  center_sq := center_sq1840
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1840.1
  jac_ok := checks1840.2.1
  accepted := checks1840.2.2

def tau1841 : RatBall :=
  ⟨⟨93/320, -17/64⟩, 3/640⟩
def center1841 : GaussianRat :=
  ⟨104546899/500000000, -171855447/1000000000⟩
def contact1841 : RatBall := localContactBall tau1841 center1841
def work1841 : RoundedTauEval :=
  evalTau precision tau1841 contact1841 logTwoBall

theorem center_sq1841 : (center1841.re : ℝ)^2 +
    (center1841.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1841]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1841 : work1841.theta.ok = true ∧
    work1841.jac.invOK = true ∧ acceptsUnitSq work1841.out = true := by
  norm_num [work1841, contact1841, tau1841, center1841, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1841 : CellCertificate where
  tauBall := tau1841
  contactCenter := center1841
  contactBall := contact1841
  work := work1841
  center_sq := center_sq1841
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1841.1
  jac_ok := checks1841.2.1
  accepted := checks1841.2.2

def tau1842 : RatBall :=
  ⟨⟨19/64, -17/64⟩, 3/640⟩
def center1842 : GaussianRat :=
  ⟨42650399/200000000, -171191029/1000000000⟩
def contact1842 : RatBall := localContactBall tau1842 center1842
def work1842 : RoundedTauEval :=
  evalTau precision tau1842 contact1842 logTwoBall

theorem center_sq1842 : (center1842.re : ℝ)^2 +
    (center1842.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1842]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1842 : work1842.theta.ok = true ∧
    work1842.jac.invOK = true ∧ acceptsUnitSq work1842.out = true := by
  norm_num [work1842, contact1842, tau1842, center1842, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1842 : CellCertificate where
  tauBall := tau1842
  contactCenter := center1842
  contactBall := contact1842
  work := work1842
  center_sq := center_sq1842
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1842.1
  jac_ok := checks1842.2.1
  accepted := checks1842.2.2

def tau1843 : RatBall :=
  ⟨⟨89/320, -83/320⟩, 3/640⟩
def center1843 : GaussianRat :=
  ⟨100043853/500000000, -84478333/500000000⟩
def contact1843 : RatBall := localContactBall tau1843 center1843
def work1843 : RoundedTauEval :=
  evalTau precision tau1843 contact1843 logTwoBall

theorem center_sq1843 : (center1843.re : ℝ)^2 +
    (center1843.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1843]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1843 : work1843.theta.ok = true ∧
    work1843.jac.invOK = true ∧ acceptsUnitSq work1843.out = true := by
  norm_num [work1843, contact1843, tau1843, center1843, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1843 : CellCertificate where
  tauBall := tau1843
  contactCenter := center1843
  contactBall := contact1843
  work := work1843
  center_sq := center_sq1843
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1843.1
  jac_ok := checks1843.2.1
  accepted := checks1843.2.2

def tau1844 : RatBall :=
  ⟨⟨91/320, -83/320⟩, 3/640⟩
def center1844 : GaussianRat :=
  ⟨204274783/1000000000, -168328783/1000000000⟩
def contact1844 : RatBall := localContactBall tau1844 center1844
def work1844 : RoundedTauEval :=
  evalTau precision tau1844 contact1844 logTwoBall

theorem center_sq1844 : (center1844.re : ℝ)^2 +
    (center1844.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1844]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1844 : work1844.theta.ok = true ∧
    work1844.jac.invOK = true ∧ acceptsUnitSq work1844.out = true := by
  norm_num [work1844, contact1844, tau1844, center1844, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1844 : CellCertificate where
  tauBall := tau1844
  contactCenter := center1844
  contactBall := contact1844
  work := work1844
  center_sq := center_sq1844
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1844.1
  jac_ok := checks1844.2.1
  accepted := checks1844.2.2

def tau1845 : RatBall :=
  ⟨⟨89/320, -81/320⟩, 3/640⟩
def center1845 : GaussianRat :=
  ⟨199473497/1000000000, -41191221/250000000⟩
def contact1845 : RatBall := localContactBall tau1845 center1845
def work1845 : RoundedTauEval :=
  evalTau precision tau1845 contact1845 logTwoBall

theorem center_sq1845 : (center1845.re : ℝ)^2 +
    (center1845.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1845]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1845 : work1845.theta.ok = true ∧
    work1845.jac.invOK = true ∧ acceptsUnitSq work1845.out = true := by
  norm_num [work1845, contact1845, tau1845, center1845, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1845 : CellCertificate where
  tauBall := tau1845
  contactCenter := center1845
  contactBall := contact1845
  work := work1845
  center_sq := center_sq1845
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1845.1
  jac_ok := checks1845.2.1
  accepted := checks1845.2.2

def tau1846 : RatBall :=
  ⟨⟨91/320, -81/320⟩, 3/640⟩
def center1846 : GaussianRat :=
  ⟨101825843/500000000, -82077687/500000000⟩
def contact1846 : RatBall := localContactBall tau1846 center1846
def work1846 : RoundedTauEval :=
  evalTau precision tau1846 contact1846 logTwoBall

theorem center_sq1846 : (center1846.re : ℝ)^2 +
    (center1846.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1846]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1846 : work1846.theta.ok = true ∧
    work1846.jac.invOK = true ∧ acceptsUnitSq work1846.out = true := by
  norm_num [work1846, contact1846, tau1846, center1846, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1846 : CellCertificate where
  tauBall := tau1846
  contactCenter := center1846
  contactBall := contact1846
  work := work1846
  center_sq := center_sq1846
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1846.1
  jac_ok := checks1846.2.1
  accepted := checks1846.2.2

def tau1847 : RatBall :=
  ⟨⟨93/320, -83/320⟩, 3/640⟩
def center1847 : GaussianRat :=
  ⟨52110811/250000000, -167692033/1000000000⟩
def contact1847 : RatBall := localContactBall tau1847 center1847
def work1847 : RoundedTauEval :=
  evalTau precision tau1847 contact1847 logTwoBall

theorem center_sq1847 : (center1847.re : ℝ)^2 +
    (center1847.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1847]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1847 : work1847.theta.ok = true ∧
    work1847.jac.invOK = true ∧ acceptsUnitSq work1847.out = true := by
  norm_num [work1847, contact1847, tau1847, center1847, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1847 : CellCertificate where
  tauBall := tau1847
  contactCenter := center1847
  contactBall := contact1847
  work := work1847
  center_sq := center_sq1847
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1847.1
  jac_ok := checks1847.2.1
  accepted := checks1847.2.2

def cells : List CellCertificate := [cell1840, cell1841, cell1842, cell1843, cell1844, cell1845, cell1846, cell1847]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0230
