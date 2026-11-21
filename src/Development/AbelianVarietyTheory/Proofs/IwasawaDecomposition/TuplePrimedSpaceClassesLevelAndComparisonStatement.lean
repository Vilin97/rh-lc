module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TuplePrimedSpaceClassesLevelAndComparison
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) (KP : ClsPTied (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal ∧ ∀ j, ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∉ v.asIdeal) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → ∃ K : ClassesAtPrimes (I.fm l u a) (badQ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) Q), K.lev.Lb = KP.lev.Lb ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) ∧ I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧ (∀ v ∈ badG (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G), K.lev.Uloc v = KP.lev.Uloc v) ∧ ∀ (κ : K.lev.U) (κ' : KP.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) κ.1 = 1) → K.lev.chi κ = KP.lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes | exact GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes | (intros; apply GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes <;> assumption)
