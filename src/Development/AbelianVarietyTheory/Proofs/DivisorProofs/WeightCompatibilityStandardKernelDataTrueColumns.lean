module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGapStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)

noncomputable section

namespace GlobalTheory.ColRows


set_option maxHeartbeats 1000000 in
theorem weightTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (Gi : G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L) (Gl : G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (K : G.Consts) (Y : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (cX : ExtraC) (ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).s.Del = (Del : ℚ) → L.etaSz = ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L Del h0) W pl (t.word u) (letterOf (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L Del h0 u) := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
  obtain ⟨hX, -, hPr, -, -, -, hword, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  subst hX
  cases hPr
  cases hword
  cases hW
  have hN := GlobalTheory.T.columnNormParameters_eq_natStepGap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L Del h0 hDel hEta
  refine ⟨plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G), fun u => ?_⟩
  have key := GlobalTheory.CoreHt.weightTie_trueCols I hOk l Z L ⟨Del, hDel⟩ u
  have gen : ∀ N : NumDatum, numDatumOfParameters (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L = N → ∀ (W' : Wts B.fields (B.primes X).Word N.R), HEq B.wts W' →
      ∀ (pl' : RPl N.R ≃ B.fields.Tau), HEq (plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) pl' → ∀ δ : Code N, HEq (codeRec L u) δ →
      GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie N (X := B.fields) (Pr := B.primes X) W' pl' u δ := by
    intro N hN W' hW' pl' hpl δ hδ
    subst hN
    cases hW'
    cases hpl
    cases hδ
    exact key
  exact gen _ hN _ HEq.rfl _ HEq.rfl _ HEq.rfl

end GlobalTheory.ColRows

end
