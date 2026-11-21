module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumnStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClassesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctionaStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem herm_rest_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ w.asIdeal) (a : intV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E w), (a : TensorProduct (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (w.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) = inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (w.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((A u).piU : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) H A, ∀ u, (X0 u).piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    have h1 := (hT.piU u).symm.trans (hS u).1.piU
    have h2 := (hT.piU (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).u₀).symm.trans (hS _).1.piU
    rw [h1, h2]
    exact hP.cof u
  · intro u pb hpb
    exact ⟨GlobalTheory.T.baseLatticeStepZero_add_conjGeneratorDual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb, GlobalTheory.T.chart_base_lattice_sup_dual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb⟩
  · refine ⟨fun u i h1 hm v β => ?_⟩
    by_cases h2 : i + 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m
    · exact (GlobalTheory.T.chartLevelFunctionals_intermediateSteps_trueColumns I hOk hP l Z H F A hS hH hT u i h1 h2 v β).some
    · have he : i = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m := by omega
      subst he
      exact (GlobalTheory.T.levelFunctional_chart_lastStep_classes I hOk hP l Z H F A hS hH hT u h1 v β).some
  · choose x hx using GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals I hOk hP l Z H F A hS hH hT hπ
    exact ⟨x, hx⟩

end GlobalTheory.Mem.Col2.TC
