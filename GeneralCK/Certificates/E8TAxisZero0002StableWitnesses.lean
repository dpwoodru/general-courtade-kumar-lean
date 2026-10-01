import GeneralCK.Certificates.E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0002StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨16620951598713310515991793134470960105966667927, 16620951598713310515991793134470960105966667928⟩
def centerDExp : DyadicInterval precision := ⟨1428634928244308711378823712010396600887434155037, 1428634928244308711378823712010396603086457410590⟩
def centerDLog : DyadicInterval precision := ⟨996509296687561598184276445757911818881532200755, 996509296687561598184276445757911821080555456308⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1428634928244308711378823712010396601437189968925, scale precision, 1428634928244308711378823712010396602536701596702, scale precision,
    0, 128, 0, 128, ⟨-33241903197426621031983586268941920774337701223, -33241903197426621031983586268941920774335604070⟩, ⟨-33241903197426621031983586268941919649531067638, -33241903197426621031983586268941919649528970485⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨17887451800319839290372054347300106957639710412, 17887451800319839290372054347300106957639710413⟩
def centerCExp : DyadicInterval precision := ⟨1426161035184028525298037043722834741256924120264, 1426161035184028525298037043722834743455947375817⟩
def centerCLog : DyadicInterval precision := ⟨995257747843394008246053613269947662197904331132, 995257747843394008246053613269947664396927586685⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1426161035184028525298037043722834741806679934152, scale precision, 1426161035184028525298037043722834742906191561929, scale precision,
    0, 128, 0, 128, ⟨-35774903600639678580744108694600214478659360220, -35774903600639678580744108694600214478657263067⟩, ⟨-35774903600639678580744108694600213351901578583, -35774903600639678580744108694600213351899481430⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨34513994673849056249355123398713418481189360346, 34513994673849056249355123398713418481189360347⟩
def centerBExp : DyadicInterval precision := ⟨1394078409980602946896329831479021586411470776403, 1394078409980602946896329831479021588610494031956⟩
def centerBLog : DyadicInterval precision := ⟨978929238224557456986699259969584039246976828266, 978929238224557456986699259969584041446000083819⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1394078409980602946896329831479021586961226590291, scale precision, 1394078409980602946896329831479021588060738218068, scale precision,
    0, 128, 0, 128, ⟨-69027989347698112498710246797426837538723980884, -69027989347698112498710246797426837538721883731⟩, ⟨-69027989347698112498710246797426836386035557654, -69027989347698112498710246797426836386033460501⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨16146021631622132505602154469507921559441792473, 17095885651040514825842973106213884464633028209⟩
def wholeDExp : DyadicInterval precision := ⟨1427706722737910795912950268245206059093886102271, 1429563729219877177794428923148060136729147575503⟩
def wholeDLog : DyadicInterval precision := ⟨996039840755618551298709894112357433764303697906, 996978902895462305330196666434672379232603104095⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1427706722737910795912950268245206059643641916159, scale precision, 1429563729219877177794428923148060136179391761615, scale precision,
    0, 128, 0, 128, ⟨-34191771302081029651685946212427769492036061204, -34191771302081029651685946212427769492033964051⟩, ⟨-32292043263244265011204308939015842556846715446, -32292043263244265011204308939015842556844618293⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨16146021631622132505602154469507921559441792473, 19628941078537730196812941240615820545473948722⟩
def wholeCExp : DyadicInterval precision := ⟨1422766325265285935775877612508304620426744726032, 1429563729219877177794428923148060136729147575503⟩
def wholeCLog : DyadicInterval precision := ⟨993538609139131549366545609183574417798866669948, 996978902895462305330196666434672379232603104095⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1422766325265285935775877612508304620976500539920, scale precision, 1429563729219877177794428923148060136179391761615, scale precision,
    0, 128, 0, 128, ⟨-39257882157075460393625882481231641655672054699, -39257882157075460393625882481231641655669957546⟩, ⟨-32292043263244265011204308939015842556846715446, -32292043263244265011204308939015842556844618293⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨32296631088779800838933709755643288761184366277, 36731543043628067898155960956801315285829304374⟩
def wholeBExp : DyadicInterval precision := ⟨1389854329341637920452395630847774504872918950707, 1398314974961442163854890103597640425462105602732⟩
def wholeBLog : DyadicInterval precision := ⟨976765729861290771806028354487818354829744711949, 981095928713060143440614067544145824500769419918⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1389854329341637920452395630847774505422674764595, scale precision, 1398314974961442163854890103597640424912349788844, scale precision,
    0, 128, 0, 128, ⟨-73463086087256135796311921913602631149755508930, -73463086087256135796311921913602631149753411777⟩, ⟨-64593262177559601677867419511286576947771756711, -64593262177559601677867419511286576947769659558⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0002StableWitnesses
