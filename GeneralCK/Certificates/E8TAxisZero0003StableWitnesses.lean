import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0003StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨15671095633019860897215209866369230294530182688, 15671095633019860897215209866369230294530182689⟩
def centerDExp : DyadicInterval precision := ⟨1430493126269901616989962472786282227563085586833, 1430493126269901616989962472786282229762108842386⟩
def centerDLog : DyadicInterval precision := ⟨997448659491958118410211053001204308338128746073, 997448659491958118410211053001204310537152001626⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1430493126269901616989962472786282228112841400721, scale precision, 1430493126269901616989962472786282229212353028498, scale precision,
    0, 128, 0, 128, ⟨-31342191266039721794430419732738461150734173770, -31342191266039721794430419732738461150732076617⟩, ⟨-31342191266039721794430419732738460027388654137, -31342191266039721794430419732738460027386556984⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨16937573839142958325485834377227148560267537173, 16937573839142958325485834377227148560267537174⟩
def centerCExp : DyadicInterval precision := ⟨1428016058447464986913713547260113933228851511629, 1428016058447464986913713547260113935427874767182⟩
def centerCLog : DyadicInterval precision := ⟨996196309375885725170924381614964827977213047958, 996196309375885725170924381614964830176236303511⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1428016058447464986913713547260113933778607325517, scale precision, 1428016058447464986913713547260113934878118953294, scale precision,
    0, 128, 0, 128, ⟨-33875147678285916650971668754454297683183172569, -33875147678285916650971668754454297683181075416⟩, ⟨-33875147678285916650971668754454296557889073280, -33875147678285916650971668754454296557886976127⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨32613386452068186512645484902019899271106700537, 32613386452068186512645484902019899271106700538⟩
def centerBExp : DyadicInterval precision := ⟨1397708984828652127800670294526114219544144078877, 1397708984828652127800670294526114221743167334430⟩
def centerBLog : DyadicInterval precision := ⟨980786206259123103316407863840628217789319410175, 980786206259123103316407863840628219988342665728⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1397708984828652127800670294526114220093899892765, scale precision, 1397708984828652127800670294526114221193411520542, scale precision,
    0, 128, 0, 128, ⟨-65226772904136373025290969804039799117061596556, -65226772904136373025290969804039799117059499403⟩, ⟨-65226772904136373025290969804039797967367302749, -65226772904136373025290969804039797967365205596⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨15196173486161644112312625263859972843392477663, 16146021631622132505602154469507921559441792474⟩
def wholeDExp : DyadicInterval precision := ⟨1429563729219877177794428923148060134530124319950, 1431423120000492259122295500270501609338356151294⟩
def wholeDLog : DyadicInterval precision := ⟨996978902895462305330196666434672377033579848542, 997918566589803370182164072894784146467964879609⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1429563729219877177794428923148060135079880133838, scale precision, 1431423120000492259122295500270501608788600337406, scale precision,
    0, 128, 0, 128, ⟨-32292043263244265011204308939015843680922551602, -32292043263244265011204308939015843680920454449⟩, ⟨-30392346972323288224625250527719945125478162145, -30392346972323288224625250527719945125476064992⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨15196173486161644112312625263859972843392477663, 18679030162303741504086552505207128636420699063⟩
def wholeCExp : DyadicInterval precision := ⟨1424616997239092963457576464131988991327542522851, 1431423120000492259122295500270501609338356151294⟩
def wholeCLog : DyadicInterval precision := ⟨994476071531667759156497176411557096946142239221, 997918566589803370182164072894784146467964879609⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1424616997239092963457576464131988991877298336739, scale precision, 1431423120000492259122295500270501608788600337406, scale precision,
    0, 128, 0, 128, ⟨-37358060324607483008173105010414257836831942606, -37358060324607483008173105010414257836829845453⟩, ⟨-30392346972323288224625250527719945125478162145, -30392346972323288224625250527719945125476064992⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨30396171800123412460251093542107771996415104709, 34830775707694518323356855819802492385993843110⟩
def wholeBExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1401956297293647672601908456314651955587398897934⟩
def wholeBLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 982955633057142006343070852505364093763236165501⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1401956297293647672601908456314651955037643084046, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-60792343600246824920502187084215543419725645729, -60792343600246824920502187084215543419723548576⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0003StableWitnesses
