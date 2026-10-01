import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0000StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨18520713486944908849589682846130841202756280060, 18520713486944908849589682846130841202756280061⟩
def centerDExp : DyadicInterval precision := ⟨1424925672993232823669539261288255236086664390075, 1424925672993232823669539261288255238285687645628⟩
def centerDLog : DyadicInterval precision := ⟨994632373490912888449452118447742043824684057942, 994632373490912888449452118447742046023707313495⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1424925672993232823669539261288255236636420203963, scale precision, 1424925672993232823669539261288255237735931831740, scale precision,
    0, 128, 0, 128, ⟨-37041426973889817699179365692261682969380929891, -37041426973889817699179365692261682969378832738⟩, ⟨-37041426973889817699179365692261681841646287505, -37041426973889817699179365692261681841644190352⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643299660144, 19787261415618956269193137821462137643299660145⟩
def centerCExp : DyadicInterval precision := ⟨1422458110153910514512537297173309437352704550462, 1422458110153910514512537297173309439551727806015⟩
def centerCLog : DyadicInterval precision := ⟨993382423595496802456179790205135829228690482622, 993382423595496802456179790205135831427713738175⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1422458110153910514512537297173309437902460364350, scale precision, 1422458110153910514512537297173309439001971992127, scale precision,
    0, 128, 0, 128, ⟨-39574522831237912538386275642924275851445840514, -39574522831237912538386275642924275851443743361⟩, ⟨-39574522831237912538386275642924274721754897217, -39574522831237912538386275642924274721752800064⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨38315625879059651361002779648504240877812961677, 38315625879059651361002779648504240877812961678⟩
def centerBExp : DyadicInterval precision := ⟨1386844740094340195616466637239585533175353614045, 1386844740094340195616466637239585535374376869598⟩
def centerBLog : DyadicInterval precision := ⟨975222308904945787429848329856119060048479601589, 975222308904945787429848329856119062247502857142⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1386844740094340195616466637239585533725109427933, scale precision, 1386844740094340195616466637239585534824621055710, scale precision,
    0, 128, 0, 128, ⟨-76631251758119302722005559297008482334977348295, -76631251758119302722005559297008482334975251142⟩, ⟨-76631251758119302722005559297008481176276595570, -76631251758119302722005559297008481176274498417⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160327707, 18995665047735116218618892934888584156033732658⟩
def wholeDExp : DyadicInterval precision := ⟨1423999843327116683343282796578766319521637719281, 1425852095715601701956974364377367525255168591536⟩
def wholeDLog : DyadicInterval precision := ⟨994163517538761546318115582447098111973928863644, 995101379269639710001049868967429117197932794939⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1423999843327116683343282796578766320071393533169, scale precision, 1425852095715601701956974364377367524705412777648, scale precision,
    0, 128, 0, 128, ⟨-37991330095470232437237785869777168876302439825, -37991330095470232437237785869777168876300342672⟩, ⟨-36091532956806446805385153816125041710820745831, -36091532956806446805385153816125041710818648678⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160327707, 21528821741448843534916460983893935247377312626⟩
def wholeCExp : DyadicInterval precision := ⟨1419072076386451827323355281724057475125424745425, 1425852095715601701956974364377367525255168591536⟩
def wholeCLog : DyadicInterval precision := ⟨991665478244185565170265217796583833220263420595, 995101379269639710001049868967429117197932794939⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1419072076386451827323355281724057475675180559313, scale precision, 1425852095715601701956974364377367524705412777648, scale precision,
    0, 128, 0, 128, ⟨-43057643482897687069832921967787871060948917639, -43057643482897687069832921967787871060946820486⟩, ⟨-36091532956806446805385153816125041710820745831, -36091532956806446805385153816125041710818648678⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨36097938246870058546958457136650379086153782135, 40533518663166560848124822041176720320630938596⟩
def wholeBExp : DyadicInterval precision := ⟨1382641925933778624162051348417793950459834536220, 1391059939013504036843525882064723713679662965519⟩
def wholeBLog : DyadicInterval precision := ⟨973064230117935785593232025639809023515288350551, 977383551042037225952002295716720301818895510063⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1382641925933778624162051348417793951009590350108, scale precision, 1391059939013504036843525882064723713129907151631, scale precision,
    0, 128, 0, 128, ⟨-81067037326333121696249644082353441222374352421, -81067037326333121696249644082353441222372255268⟩, ⟨-72195876493740117093916914273300757594713787782, -72195876493740117093916914273300757594711690629⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0000StableWitnesses
