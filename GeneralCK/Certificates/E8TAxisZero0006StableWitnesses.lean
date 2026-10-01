import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0006StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨21370495222089901813019887143702178164829792486, 21370495222089901813019887143702178164829792487⟩
def centerDExp : DyadicInterval precision := ⟨1419379569827633630618157326958425743127605926610, 1419379569827633630618157326958425745326629182163⟩
def centerDLog : DyadicInterval precision := ⟨991821481258824824738644685212964217149601286016, 991821481258824824738644685212964219348624541569⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1419379569827633630618157326958425743677361740498, scale precision, 1419379569827633630618157326958425744776873368275, scale precision,
    0, 128, 0, 128, ⟨-42740990444179803626039774287404356895731217634, -42740990444179803626039774287404356895729120481⟩, ⟨-42740990444179803626039774287404355763590049465, -42740990444179803626039774287404355763587952312⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨22637124082456445254227729657395697674875674669, 22637124082456445254227729657395697674875674670⟩
def centerCExp : DyadicInterval precision := ⟨1416921454323240139594433243688361662242981673120, 1416921454323240139594433243688361664442004928673⟩
def centerCLog : DyadicInterval precision := ⟨990573920836186620650833277746320784780310117698, 990573920836186620650833277746320786979333373251⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1416921454323240139594433243688361662792737487008, scale precision, 1416921454323240139594433243688361663892249114785, scale precision,
    0, 128, 0, 128, ⟨-45274248164912890508455459314791395916805017295, -45274248164912890508455459314791395916802920142⟩, ⟨-45274248164912890508455459314791394782699778535, -45274248164912890508455459314791394782697681382⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨44019221828644720306073496201742716112992228277, 44019221828644720306073496201742716112992228278⟩
def centerBExp : DyadicInterval precision := ⟨1376062387546952102332932362773385023678422884603, 1376062387546952102332932362773385025877446140156⟩
def centerBLog : DyadicInterval precision := ⟨969679328563446229227733723859229679757920562489, 969679328563446229227733723859229681956943818042⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1376062387546952102332932362773385024228178698491, scale precision, 1376062387546952102332932362773385025327690326268, scale precision,
    0, 128, 0, 128, ⟨-88038443657289440612146992403485432809875472187, -88038443657289440612146992403485432809873375034⟩, ⟨-88038443657289440612146992403485431642095538078, -88038443657289440612146992403485431642093440925⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932455778, 22162133741881529770516429908069211989432986974⟩
def wholeDExp : DyadicInterval precision := ⟨1417842757137037989742285799922994927468086581895, 1420918019911383254566844357126927031797158658050⟩
def wholeDLog : DyadicInterval precision := ⟨991041631832012714857158240438297378656595154964, 992601745007901601457433275450218203485852649055⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1417842757137037989742285799922994928017842395783, scale precision, 1420918019911383254566844357126927031247402844162, scale precision,
    0, 128, 0, 128, ⟨-44324267483763059541032859816138424545551175676, -44324267483763059541032859816138424545549078523⟩, ⟨-41157742587080362175549384121068020958408269492, -41157742587080362175549384121068020958406172339⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932455778, 24695481355850246866248295865805301976344615012⟩
def wholeCExp : DyadicInterval precision := ⟨1412935927708083132512800521363519720725837255886, 1420918019911383254566844357126927031797158658050⟩
def wholeCLog : DyadicInterval precision := ⟨988548891914689170103698086859276755252169128429, 992601745007901601457433275450218203485852649055⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1412935927708083132512800521363519721275593069774, scale precision, 1420918019911383254566844357126927031247402844162, scale precision,
    0, 128, 0, 128, ⟨-49390962711700493732496591731610604521342406679, -49390962711700493732496591731610604521340309526⟩, ⟨-41157742587080362175549384121068020958408269492, -41157742587080362175549384121068020958406172339⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨41167241659773099362357909881550147015249154044, 46871591652396955948239255283142047275791395946⟩
def wholeBExp : DyadicInterval precision := ⟨1370701615716012189539119176421333096411901624091, 1381443388570658598756805128725695648682979353028⟩
def wholeBLog : DyadicInterval precision := ⟨966915624602095365704810787008635852288416019661, 972448215678536315612740583202668588885486229541⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1370701615716012189539119176421333096961657437979, scale precision, 1381443388570658598756805128725695648133223539140, scale precision,
    0, 128, 0, 128, ⟨-93743183304793911896478510566284095137757383212, -93743183304793911896478510566284095137755286059⟩, ⟨-82334483319546198724715819763100293448883758966, -82334483319546198724715819763100293448881661813⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0006StableWitnesses
