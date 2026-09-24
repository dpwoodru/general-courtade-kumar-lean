import GeneralCK.Certificates.E8TAxisDyadicJetKernel

/-! Exact dyadic replay of the centered arithmetic for the first bridge leaf.

The derivative intervals in this file are the outputs of the traced BJ5
evaluation.  This module checks every subsequent multiplication, division,
addition, and the final strict positivity.  A separate semantic theorem must
still prove that those derivative boxes contain the concrete E8 derivatives.
-/

namespace GeneralCK.Certificates.E8TAxisOneCellArithmetic

open DyadicInterval

def precision : ℕ := 160

def powI (a : DyadicInterval precision) : ℕ → DyadicInterval precision
  | 0 => ofInt precision 1
  | n + 1 => (powI a n).mul a

def divNat (a : DyadicInterval precision) (n : ℕ) : DyadicInterval precision :=
  a.mul (ofInt precision n).recip

def ds : DyadicInterval precision := ⟨-5480631139990885943263818122686061323709747037, 5480631139990885943263818122686061323709747037⟩
def dt : DyadicInterval precision := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩
def initial : DyadicInterval precision := ⟨96479987514856367516858255125746966456, 96479987514856367516858255125746966457⟩
def der_0_2 : DyadicInterval precision := ⟨4519210457057521137229765141354245421005, 4519210457057521137229765141354245421006⟩
def term_00 : DyadicInterval precision :=
  divNat ((der_0_2.mul (powI ds 0)).mul (powI dt 1)) 1
def der_1_1 : DyadicInterval precision := ⟨5825744588294595774549217804696951856591, 5825744588294595774549217804696951856592⟩
def term_01 : DyadicInterval precision :=
  divNat ((der_1_1.mul (powI ds 1)).mul (powI dt 0)) 1
def der_0_3 : DyadicInterval precision := ⟨118582717436939698908153654196102423982377, 118582717436939698908153654196102423982378⟩
def term_02 : DyadicInterval precision :=
  divNat ((der_0_3.mul (powI ds 0)).mul (powI dt 2)) 2
def der_1_2 : DyadicInterval precision := ⟨229186523496188191082139692016834927154521, 229186523496188191082139692016834927154522⟩
def term_03 : DyadicInterval precision :=
  divNat ((der_1_2.mul (powI ds 1)).mul (powI dt 1)) 1
def der_2_1 : DyadicInterval precision := ⟨279368631586065225204327724264734615978079, 279368631586065225204327724264734615978080⟩
def term_04 : DyadicInterval precision :=
  divNat ((der_2_1.mul (powI ds 2)).mul (powI dt 0)) 2
def der_0_4 : DyadicInterval precision := ⟨1392332258135485598173151523474367399572789, 1392332258135485598173151523474367399572790⟩
def term_05 : DyadicInterval precision :=
  divNat ((der_0_4.mul (powI ds 0)).mul (powI dt 3)) 6
def der_1_3 : DyadicInterval precision := ⟨4720977068780883704213191717654544051284798, 4720977068780883704213191717654544051284799⟩
def term_06 : DyadicInterval precision :=
  divNat ((der_1_3.mul (powI ds 1)).mul (powI dt 2)) 2
def der_2_2 : DyadicInterval precision := ⟨8688810967106778156071161810398760156686530, 8688810967106778156071161810398760156686531⟩
def term_07 : DyadicInterval precision :=
  divNat ((der_2_2.mul (powI ds 2)).mul (powI dt 1)) 2
def der_3_1 : DyadicInterval precision := ⟨9973899596571059047491509856339808284992519, 9973899596571059047491509856339808284992520⟩
def term_08 : DyadicInterval precision :=
  divNat ((der_3_1.mul (powI ds 3)).mul (powI dt 0)) 6
def der_0_5 : DyadicInterval precision := ⟨-39650124131037391327253355385768318930600639515, 39504181119357617933921129666349342106993765452⟩
def term_09 : DyadicInterval precision :=
  divNat ((der_0_5.mul (powI ds 0)).mul (powI dt 4)) 24
def der_1_4 : DyadicInterval precision := ⟨-51711515788143094325076437455461675942582110669, 51346357371845229472204442517632425325292215690⟩
def term_10 : DyadicInterval precision :=
  divNat ((der_1_4.mul (powI ds 1)).mul (powI dt 3)) 6
def der_2_3 : DyadicInterval precision := ⟨-79573223867531099897250579537987000980859222779, 79083629626869876958952174899665922714119802515⟩
def term_11 : DyadicInterval precision :=
  divNat ((der_2_3.mul (powI ds 2)).mul (powI dt 2)) 4
def der_3_2 : DyadicInterval precision := ⟨-137802679877904028449942018430273307142661469485, 137245720291106155681741642122116246242621641305⟩
def term_12 : DyadicInterval precision :=
  divNat ((der_3_2.mul (powI ds 3)).mul (powI dt 1)) 6
def der_4_1 : DyadicInterval precision := ⟨-253355451538131606042877647628360560486872739056, 253203448681657190933886061677592959756989445893⟩
def term_13 : DyadicInterval precision :=
  divNat ((der_4_1.mul (powI ds 4)).mul (powI dt 0)) 24

def centeredReplay : DyadicInterval precision :=
  ((((((((((((((initial.add term_00).add term_01).add term_02).add term_03).add term_04).add term_05).add term_06).add term_07).add term_08).add term_09).add term_10).add term_11).add term_12).add term_13)

theorem centeredReplay_positive : centeredReplay.positiveCheck = true := by decide

#print axioms centeredReplay_positive

end GeneralCK.Certificates.E8TAxisOneCellArithmetic
