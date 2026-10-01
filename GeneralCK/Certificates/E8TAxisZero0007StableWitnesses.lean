import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0007StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643299660144, 19787261415618956269193137821462137643299660145⟩
def centerDExp : DyadicInterval precision := ⟨1422458110153910514512537297173309437352704550462, 1422458110153910514512537297173309439551727806015⟩
def centerDLog : DyadicInterval precision := ⟨993382423595496802456179790205135829228690482622, 993382423595496802456179790205135831427713738175⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1422458110153910514512537297173309437902460364350, scale precision, 1422458110153910514512537297173309439001971992127, scale precision,
    0, 128, 0, 128, ⟨-39574522831237912538386275642924275851445840514, -39574522831237912538386275642924275851443743361⟩, ⟨-39574522831237912538386275642924274721754897217, -39574522831237912538386275642924274721752800064⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨21053843929995845187789694472046872430432246941, 21053843929995845187789694472046872430432246942⟩
def centerCExp : DyadicInterval precision := ⟨1419994753219220517666583706272429596750295095776, 1419994753219220517666583706272429598949318351329⟩
def centerCLog : DyadicInterval precision := ⟨992133537010893656493896321340013157096725839029, 992133537010893656493896321340013159295749094582⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1419994753219220517666583706272429597300050909664, scale precision, 1419994753219220517666583706272429598399562537441, scale precision,
    0, 128, 0, 128, ⟨-42107687859991690375579388944093745426690888159, -42107687859991690375579388944093745426688791006⟩, ⟨-42107687859991690375579388944093744295040196762, -42107687859991690375579388944093744295038099609⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨40850377929490787525132265847486563880844462280, 40850377929490787525132265847486563880844462281⟩
def centerBExp : DyadicInterval precision := ⟨1382042531548774472754394678349177424965897883659, 1382042531548774472754394678349177427164921139212⟩
def centerBLog : DyadicInterval precision := ⟨972756190746019273686271467148684857525744169409, 972756190746019273686271467148684859724767424962⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1382042531548774472754394678349177425515653697547, scale precision, 1382042531548774472754394678349177426615165325324, scale precision,
    0, 128, 0, 128, ⟨-81700755858981575050264531694973128343053428885, -81700755858981575050264531694973128343051331732⟩, ⟨-81700755858981575050264531694973127180326517392, -81700755858981575050264531694973127180324420239⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156033732657, 20578871293540181087774692060534010761932455779⟩
def wholeDExp : DyadicInterval precision := ⟨1420918019911383254566844357126927029598135402497, 1423999843327116683343282796578766321720660974834⟩
def wholeDLog : DyadicInterval precision := ⟨992601745007901601457433275450218201286829393502, 994163517538761546318115582447098114172952119197⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1420918019911383254566844357126927030147891216385, scale precision, 1423999843327116683343282796578766321170905160946, scale precision,
    0, 128, 0, 128, ⟨-41157742587080362175549384121068022089323650775, -41157742587080362175549384121068022089321553622⟩, ⟨-37991330095470232437237785869777167747834587957, -37991330095470232437237785869777167747832490804⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18995665047735116218618892934888584156033732657, 23112119987288769110966614346048366509737452060⟩
def wholeCExp : DyadicInterval precision := ⟨1416000739382545652019056606267271856467349476465, 1423999843327116683343282796578766321720660974834⟩
def wholeCLog : DyadicInterval precision := ⟨990106358699667674089767031322997499909707645129, 994163517538761546318115582447098114172952119197⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1416000739382545652019056606267271857017105290353, scale precision, 1423999843327116683343282796578766321170905160946, scale precision,
    0, 128, 0, 128, ⟨-46224239974577538221933228692096733586897282207, -46224239974577538221933228692096733586895185054⟩, ⟨-37991330095470232437237785869777167747834587957, -37991330095470232437237785869777167747832490804⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨37998801077005824018584868335497446470094208874, 43702316363191017940573234188486312291623637587⟩
def wholeBExp : DyadicInterval precision := ⟨1376659275366914708624851436993480763400185401428, 1387446151770136419623988677444135732926778635443⟩
def wholeBLog : DyadicInterval precision := ⟨969986726310514225814593545165102078801997762132, 975530863852771772001888955504779365508547212326⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1376659275366914708624851436993480763949941215316, scale precision, 1387446151770136419623988677444135732377022821555, scale precision,
    0, 128, 0, 128, ⟨-87404632726382035881146468376972625166885129536, -87404632726382035881146468376972625166883032383⟩, ⟨-75997602154011648037169736670994892361090219046, -75997602154011648037169736670994892361088121893⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0007StableWitnesses
