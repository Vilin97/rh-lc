module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuplesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdKerStdRdMark
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.oneTie_jointsAt_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (Gi : G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L) (Gl : G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (K : G.Consts) (Y : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (cX : ExtraC) (ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) hT ex.cmp) (nch : NChoice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (tp : Formalism.L2.Host.TupTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).Dt, ∃ r : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL, (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.embLL r = (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l l0 Z L hT Gi Gl K Y cX ex t C full g nch tp _htp hTw hJ htw hpi hS hC _hLv hDt hg hgf hD hLat
  obtain ⟨t', hS', hR', _, hM'⟩ := GlobalTheory.Pdv.stdKer_stdRd_mark I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨h1, h2⟩ := GlobalTheory.T.trueColumn_joints_hold_all_tuples I hOk hP l Z l0 L hT Gi Gl K Y cX ex t' C full g hTw hJ htw hpi hS' hR' hM' hC hDt hg hgf hD hLat
  exact ⟨⟨t', h1⟩, h2⟩
