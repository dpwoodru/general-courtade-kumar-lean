import GeneralCK.Certificates.DyadicFastLog

/-!
# Integer data tables for correction logarithm endpoints

The generated certificate stores only signed integer inputs, reduction
exponents, and dyadic output endpoints.  One Boolean computation checks a
whole list.  The soundness theorem reflects that computation into the real
logarithm containment facts consumed by the proved-program kernel.
-/

namespace GeneralCK.Certificates.CorrectionIntegerLogTableKernel

open GeneralCK.Certificates

structure Datum where
  z : ℤ
  exponent : ℕ
  reciprocal : Bool
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Datum.output (d : Datum) : DyadicInterval 40 := ⟨d.lo, d.hi⟩

def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo * 16777216, a.hi * 16777216⟩

theorem lift40_contains {a : DyadicInterval 40} {x : ℝ} :
    (lift40 a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift40, Int.cast_mul, Int.cast_ofNat]
  norm_num [DyadicInterval.scale]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

def Datum.check (d : Datum) : Bool :=
  if d.reciprocal then
    DyadicFastLog.check 1099511627776 d.z d.exponent 16 (lift40 d.output.neg)
  else
    DyadicFastLog.check d.z 1099511627776 d.exponent 16 (lift40 d.output)

def Datum.Sound (d : Datum) : Prop :=
  d.output.Contains (Real.log ((d.z : ℝ) / 1099511627776))

theorem Datum.sound_of_check {d : Datum} (h : d.check = true) : d.Sound := by
  unfold Datum.check at h
  split at h
  · have hc := lift40_contains.mp (DyadicFastLog.check_sound h)
    have hn := DyadicInterval.neg_sound hc
    rw [← Real.log_inv, inv_div] at hn
    simpa only [Datum.Sound, Datum.output, DyadicInterval.neg, neg_neg,
      Int.cast_ofNat] using hn
  · have hc := lift40_contains.mp (DyadicFastLog.check_sound h)
    simpa only [Datum.Sound, Datum.output, Int.cast_ofNat] using hc

def allCheck : List Datum → Bool
  | [] => true
  | d :: rest => d.check && allCheck rest

def AllSound : List Datum → Prop
  | [] => True
  | d :: rest => d.Sound ∧ AllSound rest

theorem allSound_of_allCheck {data : List Datum} (h : allCheck data = true) :
    AllSound data := by
  induction data with
  | nil => trivial
  | cons d rest ih =>
      have parts := Bool.and_eq_true_iff.mp h
      exact ⟨d.sound_of_check parts.1, ih parts.2⟩

#print axioms Datum.sound_of_check
#print axioms allSound_of_allCheck

end GeneralCK.Certificates.CorrectionIntegerLogTableKernel
