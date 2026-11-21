module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.EMt

theorem eMtTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (tp : Formalism.L2.Host.TupTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.cf l Z) nch) (C : ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)), (∀ u F G, inner ℂ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMt u F) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMt u G) = I.ipMt l u I.mu0 F G) → (∀ u (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup), a ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → ∀ F G, inner ℂ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMtTw u a F) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMtTw u a G) = I.ipMt l u a F G) → Formalism.L2.Rows.EMtTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) C t := by
  intro B X I hOk hP l Z l0 nch tp C t h0 h1
  refine ⟨fun u F G => ?_, fun u a ha F G => ?_⟩
  · rw [h0 u F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u I.mu0 (C.forms u).jM (C.forms u).per.2.1 (C.forms u).per.2.2).1 F G
  · rw [h1 u a ha F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u a (t.ptE.jM u a) (t.ptE.per u a ha).2.1 (t.ptE.per u a ha).2.2).1 F G

end GlobalTheory.Mem.Col2.EMt

end
