import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0001StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨17570823905353200298253796885578914283159635363, 17570823905353200298253796885578914283159635364⟩
def centerDExp : DyadicInterval precision := ⟨1426779112096221605837879292607267577758400287595, 1426779112096221605837879292607267579957423543148⟩
def centerDLog : DyadicInterval precision := ⟨995570534987112542562287311753608945074363304183, 995570534987112542562287311753608947273386559736⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1426779112096221605837879292607267578308156101483, scale precision, 1426779112096221605837879292607267579407667729260, scale precision,
    0, 128, 0, 128, ⟨-35141647810706400596507593771157829129455155887, -35141647810706400596507593771157829129453058734⟩, ⟨-35141647810706400596507593771157828003185482721, -35141647810706400596507593771157828003183385568⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨18837347347792335890441586986672273956520483180, 18837347347792335890441586986672273956520483181⟩
def centerCExp : DyadicInterval precision := ⟨1424308387357809551060822779449006367915237000413, 1424308387357809551060822779449006370114260255966⟩
def centerCLog : DyadicInterval precision := ⟨994319786215667360595982839376915120674104652161, 994319786215667360595982839376915122873127907714⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1424308387357809551060822779449006368464992814301, scale precision, 1424308387357809551060822779449006369564504442078, scale precision,
    0, 128, 0, 128, ⟨-37674694695584671780883173973344548477153712419, -37674694695584671780883173973344548477151615266⟩, ⟨-37674694695584671780883173973344547348930317455, -37674694695584671780883173973344547348928220302⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨36414738655787567372767384943771663269163032974, 36414738655787567372767384943771663269163032975⟩
def centerBExp : DyadicInterval precision := ⟨1390457007296089150201247600492916033760023101622, 1390457007296089150201247600492916035959046357175⟩
def centerBLog : DyadicInterval precision := ⟨977074608077038208556184078185131913450555306680, 977074608077038208556184078185131915649578562233⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1390457007296089150201247600492916034309778915510, scale precision, 1390457007296089150201247600492916035409290543287, scale precision,
    0, 128, 0, 128, ⟨-72829477311575134745534769887543327116172396986, -72829477311575134745534769887543327116170299833⟩, ⟨-72829477311575134745534769887543325960481832064, -72829477311575134745534769887543325960479734911⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633028208, 18045766478403223402692576908062521137160327708⟩
def wholeDExp : DyadicInterval precision := ⟨1425852095715601701956974364377367523056145335983, 1427706722737910795912950268245206061292909357824⟩
def wholeDLog : DyadicInterval precision := ⟨995101379269639710001049868967429114998909539386, 996039840755618551298709894112357435963326953459⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1425852095715601701956974364377367523605901149871, scale precision, 1427706722737910795912950268245206060743153543936, scale precision,
    0, 128, 0, 128, ⟨-36091532956806446805385153816125042837822662151, -36091532956806446805385153816125042837820564998⟩, ⟨-34191771302081029651685946212427768366498148783, -34191771302081029651685946212427768366496051630⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633028208, 20578871293540181087774692060534010761932455779⟩
def wholeCExp : DyadicInterval precision := ⟨1420918019911383254566844357126927029598135402497, 1427706722737910795912950268245206061292909357824⟩
def wholeCLog : DyadicInterval precision := ⟨992601745007901601457433275450218201286829393502, 996039840755618551298709894112357435963326953459⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1420918019911383254566844357126927030147891216385, scale precision, 1427706722737910795912950268245206060743153543936, scale precision,
    0, 128, 0, 128, ⟨-41157742587080362175549384121068022089323650775, -41157742587080362175549384121068022089321553622⟩, ⟨-34191771302081029651685946212427768366498148783, -34191771302081029651685946212427768366496051630⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨34197217411116296057608686704873335075949402705, 38632454867883059004928015843439109440062491347⟩
def wholeBExp : DyadicInterval precision := ⟨1386243581168110757962356618682828762093889765683, 1394682867839290040449494560757779836865701202074⟩
def wholeBLog : DyadicInterval precision := ⟨974913818515194634191299090803398235106428622793, 979238570356633093565442356204073681058797827565⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1386243581168110757962356618682828762643645579571, scale precision, 1394682867839290040449494560757779836315945388186, scale precision,
    0, 128, 0, 128, ⟨-77264909735766118009856031686878219459727648940, -77264909735766118009856031686878219459725551787⟩, ⟨-68394434822232592115217373409746669575805430906, -68394434822232592115217373409746669575803333753⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0001StableWitnesses
