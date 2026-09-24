import CKLaneM07.CE.R3Roots
import CKLaneN1.R3Excl

/-! Lane M07 row-3 octave heights: `yupOK (1/2^(k-1)) Y<k> = true` for N1's `y_upper` (boundary 08:51Z). -/

namespace CKLaneM07.CE.R3Yup

open CKLaneM07.CE.R3Roots

theorem yup17 : CKLaneN1.R3.yupOK (1 / 65536) Y17 = true := by decide +kernel

theorem yup16 : CKLaneN1.R3.yupOK (1 / 32768) Y16 = true := by decide +kernel

theorem yup15 : CKLaneN1.R3.yupOK (1 / 16384) Y15 = true := by decide +kernel

theorem yup14 : CKLaneN1.R3.yupOK (1 / 8192) Y14 = true := by decide +kernel

theorem yup13 : CKLaneN1.R3.yupOK (1 / 4096) Y13 = true := by decide +kernel

theorem yup12 : CKLaneN1.R3.yupOK (1 / 2048) Y12 = true := by decide +kernel

theorem yup11 : CKLaneN1.R3.yupOK (1 / 1024) Y11 = true := by decide +kernel

theorem yup10 : CKLaneN1.R3.yupOK (1 / 512) Y10 = true := by decide +kernel

theorem yup9 : CKLaneN1.R3.yupOK (1 / 256) Y9 = true := by decide +kernel

theorem yup8 : CKLaneN1.R3.yupOK (1 / 128) Y8 = true := by decide +kernel

theorem yup7 : CKLaneN1.R3.yupOK (1 / 64) Y7 = true := by decide +kernel

end CKLaneM07.CE.R3Yup
