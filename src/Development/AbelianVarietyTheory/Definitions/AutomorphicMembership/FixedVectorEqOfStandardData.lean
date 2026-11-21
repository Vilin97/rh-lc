module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.KerMemPin

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def TopPt (u : B.Word) (a : I.ι) (k : GA B (B.R.N B.R.m)) : Prop :=
  ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
    IsExt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (z0 X u) (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) g'.1 g.1 →
    PtOf (g * k) (tilF I.sel (I.tup a) u d)


section Tw

variable (l0 : I.Law0 l) {inQ : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup → HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) inQ} {H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)}

structure StdP {W : TwFormsTiedS (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) (E : TwPEvzS P) : Prop where

  what₂ : ∀ u a ha, I.ReadsP a (P.cls u a ha).lev.Lb (P.cls u a ha).lev.U (P.cls u a ha).lev.chi (fun c => ((P.cls u a ha).y c).1)
    (P.cls u a ha).lat fun c s => ((P.cls u a ha).stabI c s).1

  eW : ∀ u a ha z c (s : FrP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) s', s'.1 = s.1 → (P.val u a ha).eW z c s = z c s'

  z0 : ∀ u a ha h1, (P.til u a ha h1).z0 = TC.z0 X u

  eWz : ∀ u a z, E.eWz u a z = z

variable {I l Z l0} {W : TwFormsTiedS (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}

end Tw

def StdTw (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {nch : NChoice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
    {tp : Formalism.L2.Host.TupTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) cf nch} {C : ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) : Prop :=
  I.StdW l Z l0 t.forms ∧ I.StdLv l Z l0 t.lv ∧ I.StdP l Z l0 t.pt t.ptE

def EntOk {D : D7} {Y : DivX D} {Tw : TwForms D} (E : KerEnt D Y Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  (∃ kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie E (O u μ) w, ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs) ∧ AdaptedTh E O

end GlobalTheory.Mem.Col2.TC

end
