import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0005StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨22953787393551632719727143497985289631556801416, 22953787393551632719727143497985289631556801417⟩
def centerDExp : DyadicInterval precision := ⟨1416307579080234976617203231554007855493109330315, 1416307579080234976617203231554007857692132585868⟩
def centerDLog : DyadicInterval precision := ⟨990262196212108070669138906538977259922532503432, 990262196212108070669138906538977262121555758985⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1416307579080234976617203231554007856042865144203, scale precision, 1416307579080234976617203231554007857142376771980, scale precision,
    0, 128, 0, 128, ⟨-45907574787103265439454286995970579830413050428, -45907574787103265439454286995970579830410953275⟩, ⟨-45907574787103265439454286995970578695816252391, -45907574787103265439454286995970578695814155238⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨24220466060029118896113524058399908749108492980, 24220466060029118896113524058399908749108492981⟩
def centerCExp : DyadicInterval precision := ⟨1413854687358199078213875037703050622297290468702, 1413854687358199078213875037703050624496313724255⟩
def centerCLog : DyadicInterval precision := ⟨989015958654867489723299125598598771253233385874, 989015958654867489723299125598598773452256641427⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1413854687358199078213875037703050622847046282590, scale precision, 1413854687358199078213875037703050623946557910367, scale precision,
    0, 128, 0, 128, ⟨-48440932120058237792227048116799818066500637632, -48440932120058237792227048116799818066498540479⟩, ⟨-48440932120058237792227048116799816929935431441, -48440932120058237792227048116799816929933334288⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨47188546783399559438734684046034277281554052952, 47188546783399559438734684046034277281554052953⟩
def centerBExp : DyadicInterval precision := ⟨1370107217880869781974877110045552700062516438850, 1370107217880869781974877110045552702261539694403⟩
def centerBLog : DyadicInterval precision := ⟨966608865339651213022540113418688110423791416365, 966608865339651213022540113418688112622814671918⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1370107217880869781974877110045552700612272252738, scale precision, 1370107217880869781974877110045552701711783880515, scale precision,
    0, 128, 0, 128, ⟨-94377093566799118877469368092068555149536998700, -94377093566799118877469368092068555149534901547⟩, ⟨-94377093566799118877469368092068553976681310263, -94377093566799118877469368092068553976679213110⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989432986973, 23745456717760790936231587082098894243338759236⟩
def wholeDExp : DyadicInterval precision := ⟨1414774032904110256356769903186423881438634712406, 1417842757137037989742285799922994929667109837448⟩
def wholeDLog : DyadicInterval precision := ⟨989483173884649444583154341512750139258805608841, 991041631832012714857158240438297380855618410517⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1414774032904110256356769903186423881988390526294, scale precision, 1417842757137037989742285799922994929117354023560, scale precision,
    0, 128, 0, 128, ⟨-47490913435521581872463174164197789054591889912, -47490913435521581872463174164197789054589792759⟩, ⟨-44324267483763059541032859816138423412182869373, -44324267483763059541032859816138423412180772220⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨22162133741881529770516429908069211989432986973, 26278910172762769820712328120209532577634289712⟩
def wholeCExp : DyadicInterval precision := ⟨1409877619422784131283828294378918307862547641302, 1417842757137037989742285799922994929667109837448⟩
def wholeCLog : DyadicInterval precision := ⟨986993073785723638762592089261738282950696548032, 991041631832012714857158240438297380855618410517⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1409877619422784131283828294378918308412303455190, scale precision, 1417842757137037989742285799922994929117354023560, scale precision,
    0, 128, 0, 128, ⟨-52557820345525539641424656240419065725155276982, -52557820345525539641424656240419065725153179829⟩, ⟨-44324267483763059541032859816138423412182869373, -44324267483763059541032859816138423412180772220⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨44336132104644388932745897738796280177181849964, 50041379200560764912647798132580101207504646538⟩
def wholeBExp : DyadicInterval precision := ⟨1364768781850218961742407903668732584768475455358, 1375465749469112915336031076552653134255992540413⟩
def wholeBLog : DyadicInterval precision := ⟨963850893691077814713601955824195277127821752601, 969371994805781330198871946178310256493558400824⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1364768781850218961742407903668732585318231269246, scale precision, 1375465749469112915336031076552653133706236726525, scale precision,
    0, 128, 0, 128, ⟨-100082758401121529825295596265160203003732059804, -100082758401121529825295596265160203003729962651⟩, ⟨-88672264209288777865491795477592559770221506523, -88672264209288777865491795477592559770219409370⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0005StableWitnesses
