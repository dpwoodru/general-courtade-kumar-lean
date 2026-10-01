import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10496_neg : (24792801 / 125000000) ≤ -Real.log (820089 / 1000000) ∧
    -Real.log (820089 / 1000000) ≤ (198342409 / 1000000000) := by
  have h := checkLog_sound (w := (179911 / 1820089)) (n := 12)
    (lo := (24792801 / 125000000)) (hi := (198342409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820089) = 1/(820089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10496 : Bounds (-198342409 / 1000000000) (-24792801 / 125000000) (Real.log (820089 / 1000000)) := by
  have h := reflection_log_10496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10497_neg : (166185399 / 1000000000) ≤ -Real.log (125000 / 147599) ∧
    -Real.log (125000 / 147599) ≤ (830927 / 5000000) := by
  have h := checkLog_sound (w := (22599 / 272599)) (n := 12)
    (lo := (166185399 / 1000000000)) (hi := (830927 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147599 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147599 / 125000) = 1/(125000 / 147599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10497 : Bounds (166185399 / 1000000000) (830927 / 5000000) (Real.log (147599 / 125000)) := by
  have h := reflection_log_10497_neg
  have he : Real.log (147599 / 125000) = -Real.log (125000 / 147599) := by
    rw [show ((147599 / 125000) : ℝ) = ((125000 / 147599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10498_neg : (199417259 / 1000000000) ≤ -Real.log (102401 / 125000) ∧
    -Real.log (102401 / 125000) ≤ (9970863 / 50000000) := by
  have h := checkLog_sound (w := (22599 / 227401)) (n := 12)
    (lo := (199417259 / 1000000000)) (hi := (9970863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102401) = 1/(102401 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10498 : Bounds (-9970863 / 50000000) (-199417259 / 1000000000) (Real.log (102401 / 125000)) := by
  have h := reflection_log_10498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10499_neg : (33231859 / 1000000000) ≤ -Real.log (15114285199 / 15625000000) ∧
    -Real.log (15114285199 / 15625000000) ≤ (1661593 / 50000000) := by
  have h := checkLog_sound (w := (510714801 / 30739285199)) (n := 12)
    (lo := (33231859 / 1000000000)) (hi := (1661593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15114285199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15114285199) = 1/(15114285199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10499 : Bounds (-1661593 / 50000000) (-33231859 / 1000000000) (Real.log (15114285199 / 15625000000)) := by
  have h := reflection_log_10499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10500_neg : (8225849 / 250000000) ≤ -Real.log (967632032079 / 1000000000000) ∧
    -Real.log (967632032079 / 1000000000000) ≤ (32903397 / 1000000000) := by
  have h := checkLog_sound (w := (32367967921 / 1967632032079)) (n := 12)
    (lo := (8225849 / 250000000)) (hi := (32903397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967632032079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967632032079) = 1/(967632032079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10500 : Bounds (-32903397 / 1000000000) (-8225849 / 250000000) (Real.log (967632032079 / 1000000000000)) := by
  have h := reflection_log_10500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10501_neg : (363781419 / 1000000000) ≤ -Real.log (500000000000 / 719379847797) ∧
    -Real.log (500000000000 / 719379847797) ≤ (18189071 / 50000000) := by
  have h := checkLog_sound (w := (219379847797 / 1219379847797)) (n := 12)
    (lo := (363781419 / 1000000000)) (hi := (18189071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719379847797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719379847797 / 500000000000) = 1/(500000000000 / 719379847797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10501 : Bounds (363781419 / 1000000000) (18189071 / 50000000) (Real.log (719379847797 / 500000000000)) := by
  have h := reflection_log_10501_neg
  have he : Real.log (719379847797 / 500000000000) = -Real.log (500000000000 / 719379847797) := by
    rw [show ((719379847797 / 500000000000) : ℝ) = ((500000000000 / 719379847797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10502_neg : (182801329 / 500000000) ≤ -Real.log (125000000000 / 180172801047) ∧
    -Real.log (125000000000 / 180172801047) ≤ (365602659 / 1000000000) := by
  have h := checkLog_sound (w := (55172801047 / 305172801047)) (n := 12)
    (lo := (182801329 / 500000000)) (hi := (365602659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180172801047 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180172801047 / 125000000000) = 1/(125000000000 / 180172801047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10502 : Bounds (182801329 / 500000000) (365602659 / 1000000000) (Real.log (180172801047 / 125000000000)) := by
  have h := reflection_log_10502_neg
  have he : Real.log (180172801047 / 125000000000) = -Real.log (125000000000 / 180172801047) := by
    rw [show ((180172801047 / 125000000000) : ℝ) = ((125000000000 / 180172801047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10503_neg : (735449559 / 1000000000) ≤ -Real.log (500000000000 / 1043209876543) ∧
    -Real.log (500000000000 / 1043209876543) ≤ (735449561 / 1000000000) := by
  have h := checkLog_sound (w := (43209876543 / 2043209876543)) (n := 12)
    (lo := (42302379 / 1000000000)) (hi := (2115119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043209876543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043209876543 / 1000000000000) = 1/(500000000000 / 1043209876543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10503 : Bounds (735449559 / 1000000000) (735449561 / 1000000000) (Real.log (1043209876543 / 500000000000)) := by
  have h := reflection_log_10503_neg
  have he : Real.log (1043209876543 / 500000000000) = -Real.log (500000000000 / 1043209876543) := by
    rw [show ((1043209876543 / 500000000000) : ℝ) = ((500000000000 / 1043209876543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10504_neg : (737733333 / 1000000000) ≤ -Real.log (31250000000 / 65349690881) ∧
    -Real.log (31250000000 / 65349690881) ≤ (147546667 / 200000000) := by
  have h := checkLog_sound (w := (2849690881 / 127849690881)) (n := 12)
    (lo := (44586153 / 1000000000)) (hi := (22293077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65349690881 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65349690881 / 62500000000) = 1/(31250000000 / 65349690881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10504 : Bounds (737733333 / 1000000000) (147546667 / 200000000) (Real.log (65349690881 / 31250000000)) := by
  have h := reflection_log_10504_neg
  have he : Real.log (65349690881 / 31250000000) = -Real.log (31250000000 / 65349690881) := by
    rw [show ((65349690881 / 31250000000) : ℝ) = ((31250000000 / 65349690881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10505_neg : (151531587 / 500000000) ≤ -Real.log (500 / 677) ∧
    -Real.log (500 / 677) ≤ (12122527 / 40000000) := by
  have h := checkLog_sound (w := (177 / 1177)) (n := 12)
    (lo := (151531587 / 500000000)) (hi := (12122527 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677 / 500) = 1/(500 / 677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10505 : Bounds (151531587 / 500000000) (12122527 / 40000000) (Real.log (677 / 500)) := by
  have h := reflection_log_10505_neg
  have he : Real.log (677 / 500) = -Real.log (500 / 677) := by
    rw [show ((677 / 500) : ℝ) = ((500 / 677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10506_neg : (17478231 / 40000000) ≤ -Real.log (323 / 500) ∧
    -Real.log (323 / 500) ≤ (3413717 / 7812500) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 323) = 1/(323 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10506 : Bounds (-3413717 / 7812500) (-17478231 / 40000000) (Real.log (323 / 500)) := by
  have h := reflection_log_10506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10507_neg : (353937 / 1000000000) ≤ -Real.log (500000 / 500177) ∧
    -Real.log (500000 / 500177) ≤ (176969 / 500000000) := by
  have h := checkLog_sound (w := (177 / 1000177)) (n := 12)
    (lo := (353937 / 1000000000)) (hi := (176969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500177 / 500000) = 1/(500000 / 500177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10507 : Bounds (353937 / 1000000000) (176969 / 500000000) (Real.log (500177 / 500000)) := by
  have h := reflection_log_10507_neg
  have he : Real.log (500177 / 500000) = -Real.log (500000 / 500177) := by
    rw [show ((500177 / 500000) : ℝ) = ((500000 / 500177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10508_neg : (177031 / 500000000) ≤ -Real.log (499823 / 500000) ∧
    -Real.log (499823 / 500000) ≤ (354063 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 999823)) (n := 12)
    (lo := (177031 / 500000000)) (hi := (354063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499823) = 1/(499823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10508 : Bounds (-354063 / 1000000000) (-177031 / 500000000) (Real.log (499823 / 500000)) := by
  have h := reflection_log_10508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10509_neg : (165892333 / 1000000000) ≤ -Real.log (500000 / 590223) ∧
    -Real.log (500000 / 590223) ≤ (82946167 / 500000000) := by
  have h := checkLog_sound (w := (90223 / 1090223)) (n := 12)
    (lo := (165892333 / 1000000000)) (hi := (82946167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590223 / 500000) = 1/(500000 / 590223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10509 : Bounds (165892333 / 1000000000) (82946167 / 500000000) (Real.log (590223 / 500000)) := by
  have h := reflection_log_10509_neg
  have he : Real.log (590223 / 500000) = -Real.log (500000 / 590223) := by
    rw [show ((590223 / 500000) : ℝ) = ((500000 / 590223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10510_neg : (198994989 / 1000000000) ≤ -Real.log (409777 / 500000) ∧
    -Real.log (409777 / 500000) ≤ (19899499 / 100000000) := by
  have h := checkLog_sound (w := (90223 / 909777)) (n := 12)
    (lo := (198994989 / 1000000000)) (hi := (19899499 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409777) = 1/(409777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10510 : Bounds (-19899499 / 100000000) (-198994989 / 1000000000) (Real.log (409777 / 500000)) := by
  have h := reflection_log_10510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10511_neg : (166639229 / 1000000000) ≤ -Real.log (62500 / 73833) ∧
    -Real.log (62500 / 73833) ≤ (16663923 / 100000000) := by
  have h := checkLog_sound (w := (11333 / 136333)) (n := 12)
    (lo := (166639229 / 1000000000)) (hi := (16663923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73833 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73833 / 62500) = 1/(62500 / 73833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10511 : Bounds (166639229 / 1000000000) (16663923 / 100000000) (Real.log (73833 / 62500)) := by
  have h := reflection_log_10511_neg
  have he : Real.log (73833 / 62500) = -Real.log (62500 / 73833) := by
    rw [show ((73833 / 62500) : ℝ) = ((62500 / 73833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10512_neg : (200071763 / 1000000000) ≤ -Real.log (51167 / 62500) ∧
    -Real.log (51167 / 62500) ≤ (50017941 / 250000000) := by
  have h := checkLog_sound (w := (11333 / 113667)) (n := 12)
    (lo := (200071763 / 1000000000)) (hi := (50017941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51167) = 1/(51167 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10512 : Bounds (-50017941 / 250000000) (-200071763 / 1000000000) (Real.log (51167 / 62500)) := by
  have h := reflection_log_10512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10513_neg : (16716267 / 500000000) ≤ -Real.log (3777813111 / 3906250000) ∧
    -Real.log (3777813111 / 3906250000) ≤ (6686507 / 200000000) := by
  have h := checkLog_sound (w := (128436889 / 7684063111)) (n := 12)
    (lo := (16716267 / 500000000)) (hi := (6686507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3777813111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3777813111) = 1/(3777813111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10513 : Bounds (-6686507 / 200000000) (-16716267 / 500000000) (Real.log (3777813111 / 3906250000)) := by
  have h := reflection_log_10513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10514_neg : (6620531 / 200000000) ≤ -Real.log (241859810271 / 250000000000) ∧
    -Real.log (241859810271 / 250000000000) ≤ (517229 / 15625000) := by
  have h := checkLog_sound (w := (8140189729 / 491859810271)) (n := 12)
    (lo := (6620531 / 200000000)) (hi := (517229 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241859810271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241859810271) = 1/(241859810271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10514 : Bounds (-517229 / 15625000) (-6620531 / 200000000) (Real.log (241859810271 / 250000000000)) := by
  have h := reflection_log_10514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10515_neg : (182443661 / 500000000) ≤ -Real.log (500000000000 / 720175851743) ∧
    -Real.log (500000000000 / 720175851743) ≤ (364887323 / 1000000000) := by
  have h := checkLog_sound (w := (220175851743 / 1220175851743)) (n := 12)
    (lo := (182443661 / 500000000)) (hi := (364887323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720175851743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720175851743 / 500000000000) = 1/(500000000000 / 720175851743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10515 : Bounds (182443661 / 500000000) (364887323 / 1000000000) (Real.log (720175851743 / 500000000000)) := by
  have h := reflection_log_10515_neg
  have he : Real.log (720175851743 / 500000000000) = -Real.log (500000000000 / 720175851743) := by
    rw [show ((720175851743 / 500000000000) : ℝ) = ((500000000000 / 720175851743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10516_neg : (366710993 / 1000000000) ≤ -Real.log (31250000000 / 45093150859) ∧
    -Real.log (31250000000 / 45093150859) ≤ (183355497 / 500000000) := by
  have h := checkLog_sound (w := (13843150859 / 76343150859)) (n := 12)
    (lo := (366710993 / 1000000000)) (hi := (183355497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45093150859 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45093150859 / 31250000000) = 1/(31250000000 / 45093150859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10516 : Bounds (366710993 / 1000000000) (183355497 / 500000000) (Real.log (45093150859 / 31250000000)) := by
  have h := reflection_log_10516_neg
  have he : Real.log (45093150859 / 31250000000) = -Real.log (31250000000 / 45093150859) := by
    rw [show ((45093150859 / 31250000000) : ℝ) = ((31250000000 / 45093150859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10517_neg : (737733333 / 1000000000) ≤ -Real.log (100000000000 / 209119010819) ∧
    -Real.log (100000000000 / 209119010819) ≤ (147546667 / 200000000) := by
  have h := checkLog_sound (w := (9119010819 / 409119010819)) (n := 12)
    (lo := (44586153 / 1000000000)) (hi := (22293077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209119010819 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209119010819 / 200000000000) = 1/(100000000000 / 209119010819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10517 : Bounds (737733333 / 1000000000) (147546667 / 200000000) (Real.log (209119010819 / 100000000000)) := by
  have h := reflection_log_10517_neg
  have he : Real.log (209119010819 / 100000000000) = -Real.log (100000000000 / 209119010819) := by
    rw [show ((209119010819 / 100000000000) : ℝ) = ((100000000000 / 209119010819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10518_neg : (740018949 / 1000000000) ≤ -Real.log (5000000000 / 10479876161) ∧
    -Real.log (5000000000 / 10479876161) ≤ (740018951 / 1000000000) := by
  have h := checkLog_sound (w := (479876161 / 20479876161)) (n := 12)
    (lo := (46871769 / 1000000000)) (hi := (4687177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10479876161 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10479876161 / 10000000000) = 1/(5000000000 / 10479876161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10518 : Bounds (740018949 / 1000000000) (740018951 / 1000000000) (Real.log (10479876161 / 5000000000)) := by
  have h := reflection_log_10518_neg
  have he : Real.log (10479876161 / 5000000000) = -Real.log (5000000000 / 10479876161) := by
    rw [show ((10479876161 / 5000000000) : ℝ) = ((5000000000 / 10479876161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10519_neg : (151900727 / 500000000) ≤ -Real.log (200 / 271) ∧
    -Real.log (200 / 271) ≤ (60760291 / 200000000) := by
  have h := checkLog_sound (w := (71 / 471)) (n := 12)
    (lo := (151900727 / 500000000)) (hi := (60760291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271 / 200) = 1/(200 / 271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10519 : Bounds (151900727 / 500000000) (60760291 / 200000000) (Real.log (271 / 200)) := by
  have h := reflection_log_10519_neg
  have he : Real.log (271 / 200) = -Real.log (200 / 271) := by
    rw [show ((271 / 200) : ℝ) = ((200 / 271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10520_neg : (219252481 / 500000000) ≤ -Real.log (129 / 200) ∧
    -Real.log (129 / 200) ≤ (438504963 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 329)) (n := 12)
    (lo := (219252481 / 500000000)) (hi := (438504963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 129) = 1/(129 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10520 : Bounds (-438504963 / 1000000000) (-219252481 / 500000000) (Real.log (129 / 200)) := by
  have h := reflection_log_10520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10521_neg : (354937 / 1000000000) ≤ -Real.log (200000 / 200071) ∧
    -Real.log (200000 / 200071) ≤ (177469 / 500000000) := by
  have h := checkLog_sound (w := (71 / 400071)) (n := 12)
    (lo := (354937 / 1000000000)) (hi := (177469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200071 / 200000) = 1/(200000 / 200071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10521 : Bounds (354937 / 1000000000) (177469 / 500000000) (Real.log (200071 / 200000)) := by
  have h := reflection_log_10521_neg
  have he : Real.log (200071 / 200000) = -Real.log (200000 / 200071) := by
    rw [show ((200071 / 200000) : ℝ) = ((200000 / 200071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10522_neg : (355063 / 1000000000) ≤ -Real.log (199929 / 200000) ∧
    -Real.log (199929 / 200000) ≤ (44383 / 125000000) := by
  have h := checkLog_sound (w := (71 / 399929)) (n := 12)
    (lo := (355063 / 1000000000)) (hi := (44383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199929) = 1/(199929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10522 : Bounds (-44383 / 125000000) (-355063 / 1000000000) (Real.log (199929 / 200000)) := by
  have h := reflection_log_10522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10523_neg : (33269259 / 200000000) ≤ -Real.log (500000 / 590491) ∧
    -Real.log (500000 / 590491) ≤ (20793287 / 125000000) := by
  have h := checkLog_sound (w := (90491 / 1090491)) (n := 12)
    (lo := (33269259 / 200000000)) (hi := (20793287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590491 / 500000) = 1/(500000 / 590491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10523 : Bounds (33269259 / 200000000) (20793287 / 125000000) (Real.log (590491 / 500000)) := by
  have h := reflection_log_10523_neg
  have he : Real.log (590491 / 500000) = -Real.log (500000 / 590491) := by
    rw [show ((590491 / 500000) : ℝ) = ((500000 / 590491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10524_neg : (199649217 / 1000000000) ≤ -Real.log (409509 / 500000) ∧
    -Real.log (409509 / 500000) ≤ (99824609 / 500000000) := by
  have h := checkLog_sound (w := (90491 / 909509)) (n := 12)
    (lo := (199649217 / 1000000000)) (hi := (99824609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409509) = 1/(409509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10524 : Bounds (-99824609 / 500000000) (-199649217 / 1000000000) (Real.log (409509 / 500000)) := by
  have h := reflection_log_10524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10525_neg : (167093699 / 1000000000) ≤ -Real.log (200000 / 236373) ∧
    -Real.log (200000 / 236373) ≤ (1670937 / 10000000) := by
  have h := checkLog_sound (w := (36373 / 436373)) (n := 12)
    (lo := (167093699 / 1000000000)) (hi := (1670937 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236373 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236373 / 200000) = 1/(200000 / 236373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10525 : Bounds (167093699 / 1000000000) (1670937 / 10000000) (Real.log (236373 / 200000)) := by
  have h := reflection_log_10525_neg
  have he : Real.log (236373 / 200000) = -Real.log (200000 / 236373) := by
    rw [show ((236373 / 200000) : ℝ) = ((200000 / 236373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10526_neg : (200727919 / 1000000000) ≤ -Real.log (163627 / 200000) ∧
    -Real.log (163627 / 200000) ≤ (2509099 / 12500000) := by
  have h := checkLog_sound (w := (36373 / 363627)) (n := 12)
    (lo := (200727919 / 1000000000)) (hi := (2509099 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163627) = 1/(163627 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10526 : Bounds (-2509099 / 12500000) (-200727919 / 1000000000) (Real.log (163627 / 200000)) := by
  have h := reflection_log_10526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10527_neg : (1681711 / 50000000) ≤ -Real.log (38677004871 / 40000000000) ∧
    -Real.log (38677004871 / 40000000000) ≤ (33634221 / 1000000000) := by
  have h := checkLog_sound (w := (1322995129 / 78677004871)) (n := 12)
    (lo := (1681711 / 50000000)) (hi := (33634221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38677004871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38677004871) = 1/(38677004871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10527 : Bounds (-33634221 / 1000000000) (-1681711 / 50000000) (Real.log (38677004871 / 40000000000)) := by
  have h := reflection_log_10527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10528_neg : (33302921 / 1000000000) ≤ -Real.log (241811378919 / 250000000000) ∧
    -Real.log (241811378919 / 250000000000) ≤ (16651461 / 500000000) := by
  have h := checkLog_sound (w := (8188621081 / 491811378919)) (n := 12)
    (lo := (33302921 / 1000000000)) (hi := (16651461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241811378919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241811378919) = 1/(241811378919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10528 : Bounds (-16651461 / 500000000) (-33302921 / 1000000000) (Real.log (241811378919 / 250000000000)) := by
  have h := reflection_log_10528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10529_neg : (365995513 / 1000000000) ≤ -Real.log (500000000000 / 720974386399) ∧
    -Real.log (500000000000 / 720974386399) ≤ (182997757 / 500000000) := by
  have h := checkLog_sound (w := (220974386399 / 1220974386399)) (n := 12)
    (lo := (365995513 / 1000000000)) (hi := (182997757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720974386399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720974386399 / 500000000000) = 1/(500000000000 / 720974386399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10529 : Bounds (365995513 / 1000000000) (182997757 / 500000000) (Real.log (720974386399 / 500000000000)) := by
  have h := reflection_log_10529_neg
  have he : Real.log (720974386399 / 500000000000) = -Real.log (500000000000 / 720974386399) := by
    rw [show ((720974386399 / 500000000000) : ℝ) = ((500000000000 / 720974386399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10530_neg : (183910809 / 500000000) ≤ -Real.log (500000000000 / 722292164497) ∧
    -Real.log (500000000000 / 722292164497) ≤ (367821619 / 1000000000) := by
  have h := checkLog_sound (w := (222292164497 / 1222292164497)) (n := 12)
    (lo := (183910809 / 500000000)) (hi := (367821619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722292164497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722292164497 / 500000000000) = 1/(500000000000 / 722292164497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10530 : Bounds (183910809 / 500000000) (367821619 / 1000000000) (Real.log (722292164497 / 500000000000)) := by
  have h := reflection_log_10530_neg
  have he : Real.log (722292164497 / 500000000000) = -Real.log (500000000000 / 722292164497) := by
    rw [show ((722292164497 / 500000000000) : ℝ) = ((500000000000 / 722292164497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10531_neg : (740018949 / 1000000000) ≤ -Real.log (500000000000 / 1047987616099) ∧
    -Real.log (500000000000 / 1047987616099) ≤ (740018951 / 1000000000) := by
  have h := checkLog_sound (w := (47987616099 / 2047987616099)) (n := 12)
    (lo := (46871769 / 1000000000)) (hi := (4687177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1047987616099 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1047987616099 / 1000000000000) = 1/(500000000000 / 1047987616099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10531 : Bounds (740018949 / 1000000000) (740018951 / 1000000000) (Real.log (1047987616099 / 500000000000)) := by
  have h := reflection_log_10531_neg
  have he : Real.log (1047987616099 / 500000000000) = -Real.log (500000000000 / 1047987616099) := by
    rw [show ((1047987616099 / 500000000000) : ℝ) = ((500000000000 / 1047987616099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10532_neg : (148461283 / 200000000) ≤ -Real.log (5000000000 / 10503875969) ∧
    -Real.log (5000000000 / 10503875969) ≤ (742306417 / 1000000000) := by
  have h := checkLog_sound (w := (503875969 / 20503875969)) (n := 12)
    (lo := (9831847 / 200000000)) (hi := (12289809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10503875969 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10503875969 / 10000000000) = 1/(5000000000 / 10503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10532 : Bounds (148461283 / 200000000) (742306417 / 1000000000) (Real.log (10503875969 / 5000000000)) := by
  have h := reflection_log_10532_neg
  have he : Real.log (10503875969 / 5000000000) = -Real.log (5000000000 / 10503875969) := by
    rw [show ((10503875969 / 5000000000) : ℝ) = ((5000000000 / 10503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10533_neg : (304539189 / 1000000000) ≤ -Real.log (250 / 339) ∧
    -Real.log (250 / 339) ≤ (30453919 / 100000000) := by
  have h := checkLog_sound (w := (89 / 589)) (n := 12)
    (lo := (304539189 / 1000000000)) (hi := (30453919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 250) = 1/(250 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10533 : Bounds (304539189 / 1000000000) (30453919 / 100000000) (Real.log (339 / 250)) := by
  have h := reflection_log_10533_neg
  have he : Real.log (339 / 250) = -Real.log (250 / 339) := by
    rw [show ((339 / 250) : ℝ) = ((250 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10534_neg : (55007069 / 125000000) ≤ -Real.log (161 / 250) ∧
    -Real.log (161 / 250) ≤ (440056553 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 411)) (n := 12)
    (lo := (55007069 / 125000000)) (hi := (440056553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 161) = 1/(161 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10534 : Bounds (-440056553 / 1000000000) (-55007069 / 125000000) (Real.log (161 / 250)) := by
  have h := reflection_log_10534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10535_neg : (11123 / 31250000) ≤ -Real.log (250000 / 250089) ∧
    -Real.log (250000 / 250089) ≤ (355937 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 500089)) (n := 12)
    (lo := (11123 / 31250000)) (hi := (355937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250089 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250089 / 250000) = 1/(250000 / 250089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10535 : Bounds (11123 / 31250000) (355937 / 1000000000) (Real.log (250089 / 250000)) := by
  have h := reflection_log_10535_neg
  have he : Real.log (250089 / 250000) = -Real.log (250000 / 250089) := by
    rw [show ((250089 / 250000) : ℝ) = ((250000 / 250089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10536_neg : (356063 / 1000000000) ≤ -Real.log (249911 / 250000) ∧
    -Real.log (249911 / 250000) ≤ (11127 / 31250000) := by
  have h := checkLog_sound (w := (89 / 499911)) (n := 12)
    (lo := (356063 / 1000000000)) (hi := (11127 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249911) = 1/(249911 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10536 : Bounds (-11127 / 31250000) (-356063 / 1000000000) (Real.log (249911 / 250000)) := by
  have h := reflection_log_10536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10537_neg : (83399603 / 500000000) ≤ -Real.log (1000000 / 1181517) ∧
    -Real.log (1000000 / 1181517) ≤ (166799207 / 1000000000) := by
  have h := checkLog_sound (w := (181517 / 2181517)) (n := 12)
    (lo := (83399603 / 500000000)) (hi := (166799207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181517 / 1000000) = 1/(1000000 / 1181517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10537 : Bounds (83399603 / 500000000) (166799207 / 1000000000) (Real.log (1181517 / 1000000)) := by
  have h := reflection_log_10537_neg
  have he : Real.log (1181517 / 1000000) = -Real.log (1000000 / 1181517) := by
    rw [show ((1181517 / 1000000) : ℝ) = ((1000000 / 1181517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10538_neg : (50075663 / 250000000) ≤ -Real.log (818483 / 1000000) ∧
    -Real.log (818483 / 1000000) ≤ (200302653 / 1000000000) := by
  have h := checkLog_sound (w := (181517 / 1818483)) (n := 12)
    (lo := (50075663 / 250000000)) (hi := (200302653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818483) = 1/(818483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10538 : Bounds (-200302653 / 1000000000) (-50075663 / 250000000) (Real.log (818483 / 1000000)) := by
  have h := reflection_log_10538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10539_neg : (83773981 / 500000000) ≤ -Real.log (500000 / 591201) ∧
    -Real.log (500000 / 591201) ≤ (167547963 / 1000000000) := by
  have h := checkLog_sound (w := (91201 / 1091201)) (n := 12)
    (lo := (83773981 / 500000000)) (hi := (167547963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591201 / 500000) = 1/(500000 / 591201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10539 : Bounds (83773981 / 500000000) (167547963 / 1000000000) (Real.log (591201 / 500000)) := by
  have h := reflection_log_10539_neg
  have he : Real.log (591201 / 500000) = -Real.log (500000 / 591201) := by
    rw [show ((591201 / 500000) : ℝ) = ((500000 / 591201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10540_neg : (40276901 / 200000000) ≤ -Real.log (408799 / 500000) ∧
    -Real.log (408799 / 500000) ≤ (100692253 / 500000000) := by
  have h := checkLog_sound (w := (91201 / 908799)) (n := 12)
    (lo := (40276901 / 200000000)) (hi := (100692253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408799) = 1/(408799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10540 : Bounds (-100692253 / 500000000) (-40276901 / 200000000) (Real.log (408799 / 500000)) := by
  have h := reflection_log_10540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10541_neg : (33836543 / 1000000000) ≤ -Real.log (241682377599 / 250000000000) ∧
    -Real.log (241682377599 / 250000000000) ≤ (66087 / 1953125) := by
  have h := checkLog_sound (w := (8317622401 / 491682377599)) (n := 12)
    (lo := (33836543 / 1000000000)) (hi := (66087 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241682377599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241682377599) = 1/(241682377599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10541 : Bounds (-66087 / 1953125) (-33836543 / 1000000000) (Real.log (241682377599 / 250000000000)) := by
  have h := reflection_log_10541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10542_neg : (16751723 / 500000000) ≤ -Real.log (967051578711 / 1000000000000) ∧
    -Real.log (967051578711 / 1000000000000) ≤ (33503447 / 1000000000) := by
  have h := checkLog_sound (w := (32948421289 / 1967051578711)) (n := 12)
    (lo := (16751723 / 500000000)) (hi := (33503447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967051578711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967051578711) = 1/(967051578711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10542 : Bounds (-33503447 / 1000000000) (-16751723 / 500000000) (Real.log (967051578711 / 1000000000000)) := by
  have h := reflection_log_10542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10543_neg : (183550929 / 500000000) ≤ -Real.log (500000000000 / 721772474199) ∧
    -Real.log (500000000000 / 721772474199) ≤ (367101859 / 1000000000) := by
  have h := checkLog_sound (w := (221772474199 / 1221772474199)) (n := 12)
    (lo := (183550929 / 500000000)) (hi := (367101859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721772474199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721772474199 / 500000000000) = 1/(500000000000 / 721772474199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10543 : Bounds (183550929 / 500000000) (367101859 / 1000000000) (Real.log (721772474199 / 500000000000)) := by
  have h := reflection_log_10543_neg
  have he : Real.log (721772474199 / 500000000000) = -Real.log (500000000000 / 721772474199) := by
    rw [show ((721772474199 / 500000000000) : ℝ) = ((500000000000 / 721772474199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10544_neg : (92233117 / 250000000) ≤ -Real.log (31250000000 / 45193435527) ∧
    -Real.log (31250000000 / 45193435527) ≤ (368932469 / 1000000000) := by
  have h := checkLog_sound (w := (13943435527 / 76443435527)) (n := 12)
    (lo := (92233117 / 250000000)) (hi := (368932469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45193435527 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45193435527 / 31250000000) = 1/(31250000000 / 45193435527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10544 : Bounds (92233117 / 250000000) (368932469 / 1000000000) (Real.log (45193435527 / 31250000000)) := by
  have h := reflection_log_10544_neg
  have he : Real.log (45193435527 / 31250000000) = -Real.log (31250000000 / 45193435527) := by
    rw [show ((45193435527 / 31250000000) : ℝ) = ((31250000000 / 45193435527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10545_neg : (148461283 / 200000000) ≤ -Real.log (500000000000 / 1050387596899) ∧
    -Real.log (500000000000 / 1050387596899) ≤ (742306417 / 1000000000) := by
  have h := checkLog_sound (w := (50387596899 / 2050387596899)) (n := 12)
    (lo := (9831847 / 200000000)) (hi := (12289809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1050387596899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1050387596899 / 1000000000000) = 1/(500000000000 / 1050387596899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10545 : Bounds (148461283 / 200000000) (742306417 / 1000000000) (Real.log (1050387596899 / 500000000000)) := by
  have h := reflection_log_10545_neg
  have he : Real.log (1050387596899 / 500000000000) = -Real.log (500000000000 / 1050387596899) := by
    rw [show ((1050387596899 / 500000000000) : ℝ) = ((500000000000 / 1050387596899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10546_neg : (744595741 / 1000000000) ≤ -Real.log (31250000000 / 65799689441) ∧
    -Real.log (31250000000 / 65799689441) ≤ (744595743 / 1000000000) := by
  have h := checkLog_sound (w := (3299689441 / 128299689441)) (n := 12)
    (lo := (51448561 / 1000000000)) (hi := (25724281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65799689441 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65799689441 / 62500000000) = 1/(31250000000 / 65799689441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10546 : Bounds (744595741 / 1000000000) (744595743 / 1000000000) (Real.log (65799689441 / 31250000000)) := by
  have h := reflection_log_10546_neg
  have he : Real.log (65799689441 / 31250000000) = -Real.log (31250000000 / 65799689441) := by
    rw [show ((65799689441 / 31250000000) : ℝ) = ((31250000000 / 65799689441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10547_neg : (15263819 / 50000000) ≤ -Real.log (1000 / 1357) ∧
    -Real.log (1000 / 1357) ≤ (305276381 / 1000000000) := by
  have h := checkLog_sound (w := (357 / 2357)) (n := 12)
    (lo := (15263819 / 50000000)) (hi := (305276381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357 / 1000) = 1/(1000 / 1357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10547 : Bounds (15263819 / 50000000) (305276381 / 1000000000) (Real.log (1357 / 1000)) := by
  have h := reflection_log_10547_neg
  have he : Real.log (1357 / 1000) = -Real.log (1000 / 1357) := by
    rw [show ((1357 / 1000) : ℝ) = ((1000 / 1357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10548_neg : (220805277 / 500000000) ≤ -Real.log (643 / 1000) ∧
    -Real.log (643 / 1000) ≤ (88322111 / 200000000) := by
  have h := checkLog_sound (w := (357 / 1643)) (n := 12)
    (lo := (220805277 / 500000000)) (hi := (88322111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 643) = 1/(643 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10548 : Bounds (-88322111 / 200000000) (-220805277 / 500000000) (Real.log (643 / 1000)) := by
  have h := reflection_log_10548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10549_neg : (44617 / 125000000) ≤ -Real.log (1000000 / 1000357) ∧
    -Real.log (1000000 / 1000357) ≤ (356937 / 1000000000) := by
  have h := checkLog_sound (w := (357 / 2000357)) (n := 12)
    (lo := (44617 / 125000000)) (hi := (356937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000357 / 1000000) = 1/(1000000 / 1000357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10549 : Bounds (44617 / 125000000) (356937 / 1000000000) (Real.log (1000357 / 1000000)) := by
  have h := reflection_log_10549_neg
  have he : Real.log (1000357 / 1000000) = -Real.log (1000000 / 1000357) := by
    rw [show ((1000357 / 1000000) : ℝ) = ((1000000 / 1000357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10550_neg : (357063 / 1000000000) ≤ -Real.log (999643 / 1000000) ∧
    -Real.log (999643 / 1000000) ≤ (44633 / 125000000) := by
  have h := checkLog_sound (w := (357 / 1999643)) (n := 12)
    (lo := (357063 / 1000000000)) (hi := (44633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999643) = 1/(999643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10550 : Bounds (-44633 / 125000000) (-357063 / 1000000000) (Real.log (999643 / 1000000)) := by
  have h := reflection_log_10550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10551_neg : (167252757 / 1000000000) ≤ -Real.log (1000000 / 1182053) ∧
    -Real.log (1000000 / 1182053) ≤ (83626379 / 500000000) := by
  have h := checkLog_sound (w := (182053 / 2182053)) (n := 12)
    (lo := (167252757 / 1000000000)) (hi := (83626379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182053 / 1000000) = 1/(1000000 / 1182053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10551 : Bounds (167252757 / 1000000000) (83626379 / 500000000) (Real.log (1182053 / 1000000)) := by
  have h := reflection_log_10551_neg
  have he : Real.log (1182053 / 1000000) = -Real.log (1000000 / 1182053) := by
    rw [show ((1182053 / 1000000) : ℝ) = ((1000000 / 1182053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10552_neg : (25119717 / 125000000) ≤ -Real.log (817947 / 1000000) ∧
    -Real.log (817947 / 1000000) ≤ (200957737 / 1000000000) := by
  have h := checkLog_sound (w := (182053 / 1817947)) (n := 12)
    (lo := (25119717 / 125000000)) (hi := (200957737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817947) = 1/(817947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10552 : Bounds (-200957737 / 1000000000) (-25119717 / 125000000) (Real.log (817947 / 1000000)) := by
  have h := reflection_log_10552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10553_neg : (168002019 / 1000000000) ≤ -Real.log (1000000 / 1182939) ∧
    -Real.log (1000000 / 1182939) ≤ (8400101 / 50000000) := by
  have h := checkLog_sound (w := (182939 / 2182939)) (n := 12)
    (lo := (168002019 / 1000000000)) (hi := (8400101 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182939 / 1000000) = 1/(1000000 / 1182939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10553 : Bounds (168002019 / 1000000000) (8400101 / 50000000) (Real.log (1182939 / 1000000)) := by
  have h := reflection_log_10553_neg
  have he : Real.log (1182939 / 1000000) = -Real.log (1000000 / 1182939) := by
    rw [show ((1182939 / 1000000) : ℝ) = ((1000000 / 1182939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10554_neg : (202041523 / 1000000000) ≤ -Real.log (817061 / 1000000) ∧
    -Real.log (817061 / 1000000) ≤ (50510381 / 250000000) := by
  have h := checkLog_sound (w := (182939 / 1817061)) (n := 12)
    (lo := (202041523 / 1000000000)) (hi := (50510381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817061) = 1/(817061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10554 : Bounds (-50510381 / 250000000) (-202041523 / 1000000000) (Real.log (817061 / 1000000)) := by
  have h := reflection_log_10554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10555_neg : (34039503 / 1000000000) ≤ -Real.log (966533322279 / 1000000000000) ∧
    -Real.log (966533322279 / 1000000000000) ≤ (2127469 / 62500000) := by
  have h := checkLog_sound (w := (33466677721 / 1966533322279)) (n := 12)
    (lo := (34039503 / 1000000000)) (hi := (2127469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966533322279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966533322279) = 1/(966533322279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10555 : Bounds (-2127469 / 62500000) (-34039503 / 1000000000) (Real.log (966533322279 / 1000000000000)) := by
  have h := reflection_log_10555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10556_neg : (33704979 / 1000000000) ≤ -Real.log (966856705191 / 1000000000000) ∧
    -Real.log (966856705191 / 1000000000000) ≤ (1685249 / 50000000) := by
  have h := checkLog_sound (w := (33143294809 / 1966856705191)) (n := 12)
    (lo := (33704979 / 1000000000)) (hi := (1685249 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966856705191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966856705191) = 1/(966856705191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10556 : Bounds (-1685249 / 50000000) (-33704979 / 1000000000) (Real.log (966856705191 / 1000000000000)) := by
  have h := reflection_log_10556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10557_neg : (368210493 / 1000000000) ≤ -Real.log (250000000000 / 361286550351) ∧
    -Real.log (250000000000 / 361286550351) ≤ (184105247 / 500000000) := by
  have h := checkLog_sound (w := (111286550351 / 611286550351)) (n := 12)
    (lo := (368210493 / 1000000000)) (hi := (184105247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361286550351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361286550351 / 250000000000) = 1/(250000000000 / 361286550351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10557 : Bounds (368210493 / 1000000000) (184105247 / 500000000) (Real.log (361286550351 / 250000000000)) := by
  have h := reflection_log_10557_neg
  have he : Real.log (361286550351 / 250000000000) = -Real.log (250000000000 / 361286550351) := by
    rw [show ((361286550351 / 250000000000) : ℝ) = ((250000000000 / 361286550351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10558_neg : (370043543 / 1000000000) ≤ -Real.log (125000000000 / 180974706907) ∧
    -Real.log (125000000000 / 180974706907) ≤ (46255443 / 125000000) := by
  have h := checkLog_sound (w := (55974706907 / 305974706907)) (n := 12)
    (lo := (370043543 / 1000000000)) (hi := (46255443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180974706907 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180974706907 / 125000000000) = 1/(125000000000 / 180974706907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10558 : Bounds (370043543 / 1000000000) (46255443 / 125000000) (Real.log (180974706907 / 125000000000)) := by
  have h := reflection_log_10558_neg
  have he : Real.log (180974706907 / 125000000000) = -Real.log (125000000000 / 180974706907) := by
    rw [show ((180974706907 / 125000000000) : ℝ) = ((125000000000 / 180974706907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10559_neg : (744595741 / 1000000000) ≤ -Real.log (100000000000 / 210559006211) ∧
    -Real.log (100000000000 / 210559006211) ≤ (744595743 / 1000000000) := by
  have h := checkLog_sound (w := (10559006211 / 410559006211)) (n := 12)
    (lo := (51448561 / 1000000000)) (hi := (25724281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210559006211 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210559006211 / 200000000000) = 1/(100000000000 / 210559006211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10559 : Bounds (744595741 / 1000000000) (744595743 / 1000000000) (Real.log (210559006211 / 100000000000)) := by
  have h := reflection_log_10559_neg
  have he : Real.log (210559006211 / 100000000000) = -Real.log (100000000000 / 210559006211) := by
    rw [show ((210559006211 / 100000000000) : ℝ) = ((100000000000 / 210559006211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
