import CKLaneM07.FleetT.T0000
import CKLaneM07.FleetT.T0001
import CKLaneM07.FleetT.T0002
import CKLaneM07.FleetT.T0003
import CKLaneM07.FleetT.T0004
import CKLaneM07.FleetT.T0005
import CKLaneM07.FleetT.T0006
import CKLaneM07.FleetT.T0007
import CKLaneM07.FleetT.T0008
import CKLaneM07.FleetT.T0009
import CKLaneM07.FleetT.T0010
import CKLaneM07.FleetT.T0011
import CKLaneM07.FleetT.T0012
import CKLaneM07.FleetT.T0013
import CKLaneM07.FleetT.T0014
import CKLaneM07.FleetT.T0015
import CKLaneM07.FleetT.T0016
import CKLaneM07.FleetT.T0017
import CKLaneM07.FleetT.T0018
import CKLaneM07.FleetT.T0019
import CKLaneM07.FleetT.T0020
import CKLaneM07.FleetT.T0021
import CKLaneM07.FleetT.T0022
import CKLaneM07.FleetT.T0023
import CKLaneM07.FleetT.T0024
import CKLaneM07.FleetT.T0025
import CKLaneM07.FleetT.T0026
import CKLaneM07.FleetT.T0027
import CKLaneM07.FleetT.T0028
import CKLaneM07.FleetT.T0029
import CKLaneM07.FleetT.T0030
import CKLaneM07.FleetT.T0031
import CKLaneM07.FleetT.T0032
import CKLaneM07.G3Adapter

/-!
# Lane M07: all archived same-side `derivative` leaves

`allLeaves` is the concatenation of the 33 fleet shards (3205 leaves, each an archived
path of `same_side/ADAPT_RESULT.json` with owner `derivative`, sha256
b134020b83227cdfb54ec8a85cebf00a67bc2537320b0731836fbc8f324fe9c8).  `allLeaves_sound` proves the semantic owner statement
`SemSBox (ssBox p)` on the exact archived leaf box of every path `p`.
-/

set_option maxRecDepth 100000

namespace CKLaneM07.Leaves
open CKLaneM07

theorem sound_append {L1 L2 : List (List ℕ × Wit)}
    (h1 : ∀ x ∈ L1, SemSBox (ssBox x.1)) (h2 : ∀ x ∈ L2, SemSBox (ssBox x.1)) :
    ∀ x ∈ L1 ++ L2, SemSBox (ssBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

/-- All archived derivative leaves with their witnesses. -/
def allLeaves : List (List ℕ × Wit) :=
  CKLaneM07.FleetT.T0000.L ++ (CKLaneM07.FleetT.T0001.L ++ (CKLaneM07.FleetT.T0002.L ++ (CKLaneM07.FleetT.T0003.L ++ (CKLaneM07.FleetT.T0004.L ++ (CKLaneM07.FleetT.T0005.L ++ (CKLaneM07.FleetT.T0006.L ++ (CKLaneM07.FleetT.T0007.L ++ (CKLaneM07.FleetT.T0008.L ++ (CKLaneM07.FleetT.T0009.L ++ (CKLaneM07.FleetT.T0010.L ++ (CKLaneM07.FleetT.T0011.L ++ (CKLaneM07.FleetT.T0012.L ++ (CKLaneM07.FleetT.T0013.L ++ (CKLaneM07.FleetT.T0014.L ++ (CKLaneM07.FleetT.T0015.L ++ (CKLaneM07.FleetT.T0016.L ++ (CKLaneM07.FleetT.T0017.L ++ (CKLaneM07.FleetT.T0018.L ++ (CKLaneM07.FleetT.T0019.L ++ (CKLaneM07.FleetT.T0020.L ++ (CKLaneM07.FleetT.T0021.L ++ (CKLaneM07.FleetT.T0022.L ++ (CKLaneM07.FleetT.T0023.L ++ (CKLaneM07.FleetT.T0024.L ++ (CKLaneM07.FleetT.T0025.L ++ (CKLaneM07.FleetT.T0026.L ++ (CKLaneM07.FleetT.T0027.L ++ (CKLaneM07.FleetT.T0028.L ++ (CKLaneM07.FleetT.T0029.L ++ (CKLaneM07.FleetT.T0030.L ++ (CKLaneM07.FleetT.T0031.L ++ (CKLaneM07.FleetT.T0032.L))))))))))))))))))))))))))))))))

/-- The archived derivative paths. -/
def derivativePaths : List (List ℕ) := allLeaves.map Prod.fst

theorem allLeaves_sound : ∀ x ∈ allLeaves, SemSBox (ssBox x.1) :=
  sound_append CKLaneM07.FleetT.T0000.L_sound (sound_append CKLaneM07.FleetT.T0001.L_sound (sound_append CKLaneM07.FleetT.T0002.L_sound (sound_append CKLaneM07.FleetT.T0003.L_sound (sound_append CKLaneM07.FleetT.T0004.L_sound (sound_append CKLaneM07.FleetT.T0005.L_sound (sound_append CKLaneM07.FleetT.T0006.L_sound (sound_append CKLaneM07.FleetT.T0007.L_sound (sound_append CKLaneM07.FleetT.T0008.L_sound (sound_append CKLaneM07.FleetT.T0009.L_sound (sound_append CKLaneM07.FleetT.T0010.L_sound (sound_append CKLaneM07.FleetT.T0011.L_sound (sound_append CKLaneM07.FleetT.T0012.L_sound (sound_append CKLaneM07.FleetT.T0013.L_sound (sound_append CKLaneM07.FleetT.T0014.L_sound (sound_append CKLaneM07.FleetT.T0015.L_sound (sound_append CKLaneM07.FleetT.T0016.L_sound (sound_append CKLaneM07.FleetT.T0017.L_sound (sound_append CKLaneM07.FleetT.T0018.L_sound (sound_append CKLaneM07.FleetT.T0019.L_sound (sound_append CKLaneM07.FleetT.T0020.L_sound (sound_append CKLaneM07.FleetT.T0021.L_sound (sound_append CKLaneM07.FleetT.T0022.L_sound (sound_append CKLaneM07.FleetT.T0023.L_sound (sound_append CKLaneM07.FleetT.T0024.L_sound (sound_append CKLaneM07.FleetT.T0025.L_sound (sound_append CKLaneM07.FleetT.T0026.L_sound (sound_append CKLaneM07.FleetT.T0027.L_sound (sound_append CKLaneM07.FleetT.T0028.L_sound (sound_append CKLaneM07.FleetT.T0029.L_sound (sound_append CKLaneM07.FleetT.T0030.L_sound (sound_append CKLaneM07.FleetT.T0031.L_sound (CKLaneM07.FleetT.T0032.L_sound))))))))))))))))))))))))))))))))

/-- **Population theorem**: every archived derivative leaf box satisfies the owner statement. -/
theorem derivative_leaves_sem : ∀ p ∈ derivativePaths, SemSBox (ssBox p) := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact allLeaves_sound x hx

theorem derivativePaths_length : derivativePaths.length = 3205 := by decide +kernel

/-- **Population theorem, canonical form** (`CKLaneG3.SCover`, BRIEF §7): every archived derivative
leaf path carries the `SS_Compact` per-leaf obligation on the canonical box `CKLaneG3.sBox p`. -/
theorem derivative_sLeafOK : ∀ p ∈ derivativePaths, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun p hp => sLeafOK_of_semSBox (derivative_leaves_sem p hp)

end CKLaneM07.Leaves
