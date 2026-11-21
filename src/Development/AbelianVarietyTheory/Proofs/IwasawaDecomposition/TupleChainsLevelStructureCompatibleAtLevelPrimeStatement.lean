module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainsLevelStructureCompatibleAtLevelPrime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChains_levelStructure_compatible_at_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.tw l l0 Z) T J F), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → (∃ Lv : SymmetricTwistedLevelData W, I.StdLv l Z l0 Lv) ∧ Nonempty (TwLvSameS W) := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same | exact GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same | (intros; apply GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same <;> assumption)
