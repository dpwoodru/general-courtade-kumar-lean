import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1816 : RatBall :=
  ⟨⟨83/320, -89/320⟩, 3/640⟩
def center1816 : GaussianRat :=
  ⟨189282071/1000000000, -183581561/1000000000⟩
def contact1816 : RatBall := localContactBall tau1816 center1816
def work1816 : RoundedTauEval :=
  evalTau precision tau1816 contact1816 logTwoBall

theorem center_sq1816 : (center1816.re : ℝ)^2 +
    (center1816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1816 : work1816.theta.ok = true ∧
    work1816.jac.invOK = true ∧ acceptsUnitSq work1816.out = true := by
  norm_num [work1816, contact1816, tau1816, center1816, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1816 : CellCertificate where
  tauBall := tau1816
  contactCenter := center1816
  contactBall := contact1816
  work := work1816
  center_sq := center_sq1816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1816.1
  jac_ok := checks1816.2.1
  accepted := checks1816.2.2

def tau1817 : RatBall :=
  ⟨⟨17/64, -91/320⟩, 3/640⟩
def center1817 : GaussianRat :=
  ⟨97111567/500000000, -37439051/200000000⟩
def contact1817 : RatBall := localContactBall tau1817 center1817
def work1817 : RoundedTauEval :=
  evalTau precision tau1817 contact1817 logTwoBall

theorem center_sq1817 : (center1817.re : ℝ)^2 +
    (center1817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1817 : work1817.theta.ok = true ∧
    work1817.jac.invOK = true ∧ acceptsUnitSq work1817.out = true := by
  norm_num [work1817, contact1817, tau1817, center1817, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1817 : CellCertificate where
  tauBall := tau1817
  contactCenter := center1817
  contactBall := contact1817
  work := work1817
  center_sq := center_sq1817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1817.1
  jac_ok := checks1817.2.1
  accepted := checks1817.2.2

def tau1818 : RatBall :=
  ⟨⟨87/320, -91/320⟩, 3/640⟩
def center1818 : GaussianRat :=
  ⟨49621711/250000000, -186511513/1000000000⟩
def contact1818 : RatBall := localContactBall tau1818 center1818
def work1818 : RoundedTauEval :=
  evalTau precision tau1818 contact1818 logTwoBall

theorem center_sq1818 : (center1818.re : ℝ)^2 +
    (center1818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1818 : work1818.theta.ok = true ∧
    work1818.jac.invOK = true ∧ acceptsUnitSq work1818.out = true := by
  norm_num [work1818, contact1818, tau1818, center1818, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1818 : CellCertificate where
  tauBall := tau1818
  contactCenter := center1818
  contactBall := contact1818
  work := work1818
  center_sq := center_sq1818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1818.1
  jac_ok := checks1818.2.1
  accepted := checks1818.2.2

def tau1819 : RatBall :=
  ⟨⟨17/64, -89/320⟩, 3/640⟩
def center1819 : GaussianRat :=
  ⟨24194269/125000000, -5716477/31250000⟩
def contact1819 : RatBall := localContactBall tau1819 center1819
def work1819 : RoundedTauEval :=
  evalTau precision tau1819 contact1819 logTwoBall

theorem center_sq1819 : (center1819.re : ℝ)^2 +
    (center1819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1819 : work1819.theta.ok = true ∧
    work1819.jac.invOK = true ∧ acceptsUnitSq work1819.out = true := by
  norm_num [work1819, contact1819, tau1819, center1819, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1819 : CellCertificate where
  tauBall := tau1819
  contactCenter := center1819
  contactBall := contact1819
  work := work1819
  center_sq := center_sq1819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1819.1
  jac_ok := checks1819.2.1
  accepted := checks1819.2.2

def tau1820 : RatBall :=
  ⟨⟨87/320, -89/320⟩, 3/640⟩
def center1820 : GaussianRat :=
  ⟨7912299/40000000, -91131277/500000000⟩
def contact1820 : RatBall := localContactBall tau1820 center1820
def work1820 : RoundedTauEval :=
  evalTau precision tau1820 contact1820 logTwoBall

theorem center_sq1820 : (center1820.re : ℝ)^2 +
    (center1820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1820 : work1820.theta.ok = true ∧
    work1820.jac.invOK = true ∧ acceptsUnitSq work1820.out = true := by
  norm_num [work1820, contact1820, tau1820, center1820, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1820 : CellCertificate where
  tauBall := tau1820
  contactCenter := center1820
  contactBall := contact1820
  work := work1820
  center_sq := center_sq1820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1820.1
  jac_ok := checks1820.2.1
  accepted := checks1820.2.2

def tau1821 : RatBall :=
  ⟨⟨89/320, -93/320⟩, 3/640⟩
def center1821 : GaussianRat :=
  ⟨50860061/250000000, -2969643/15625000⟩
def contact1821 : RatBall := localContactBall tau1821 center1821
def work1821 : RoundedTauEval :=
  evalTau precision tau1821 contact1821 logTwoBall

theorem center_sq1821 : (center1821.re : ℝ)^2 +
    (center1821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1821 : work1821.theta.ok = true ∧
    work1821.jac.invOK = true ∧ acceptsUnitSq work1821.out = true := by
  norm_num [work1821, contact1821, tau1821, center1821, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1821 : CellCertificate where
  tauBall := tau1821
  contactCenter := center1821
  contactBall := contact1821
  work := work1821
  center_sq := center_sq1821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1821.1
  jac_ok := checks1821.2.1
  accepted := checks1821.2.2

def tau1822 : RatBall :=
  ⟨⟨89/320, -91/320⟩, 3/640⟩
def center1822 : GaussianRat :=
  ⟨202731249/1000000000, -37163483/200000000⟩
def contact1822 : RatBall := localContactBall tau1822 center1822
def work1822 : RoundedTauEval :=
  evalTau precision tau1822 contact1822 logTwoBall

theorem center_sq1822 : (center1822.re : ℝ)^2 +
    (center1822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1822 : work1822.theta.ok = true ∧
    work1822.jac.invOK = true ∧ acceptsUnitSq work1822.out = true := by
  norm_num [work1822, contact1822, tau1822, center1822, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1822 : CellCertificate where
  tauBall := tau1822
  contactCenter := center1822
  contactBall := contact1822
  work := work1822
  center_sq := center_sq1822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1822.1
  jac_ok := checks1822.2.1
  accepted := checks1822.2.2

def tau1823 : RatBall :=
  ⟨⟨91/320, -91/320⟩, 3/640⟩
def center1823 : GaussianRat :=
  ⟨51739029/250000000, -46278317/250000000⟩
def contact1823 : RatBall := localContactBall tau1823 center1823
def work1823 : RoundedTauEval :=
  evalTau precision tau1823 contact1823 logTwoBall

theorem center_sq1823 : (center1823.re : ℝ)^2 +
    (center1823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1823 : work1823.theta.ok = true ∧
    work1823.jac.invOK = true ∧ acceptsUnitSq work1823.out = true := by
  norm_num [work1823, contact1823, tau1823, center1823, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1823 : CellCertificate where
  tauBall := tau1823
  contactCenter := center1823
  contactBall := contact1823
  work := work1823
  center_sq := center_sq1823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1823.1
  jac_ok := checks1823.2.1
  accepted := checks1823.2.2

def cells : List CellCertificate := [cell1816, cell1817, cell1818, cell1819, cell1820, cell1821, cell1822, cell1823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227
