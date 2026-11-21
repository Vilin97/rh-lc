module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tw_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hO : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {nch : NChoice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
    {tp : Formalism.L2.Host.TupTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) cf nch} {C : ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Tw : TwForms (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
    (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (he : Tw = I.tw l l0 Z) (hC : I.StdC l Z C) (hTw : I.StdTw l Z l0 (he ▸ t))
    (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) (ha : a ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0) (h1 : 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m) :
    IsUnit (Formalism.L2.Forms.bZ u (t.pt.til u a ha h1).z0).det → ∀ (ψ : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).PTw u a).Wz) (c : (Tw.fm u a).clsP)
      (P : MvPolynomial ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tau × Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m) × Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m)) ℂ),
      P ∈ Formalism.L2.Forms.CSpan (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).lam (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m) →
      (∀ s, t.ptE.eWz u a ψ c s =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m)) (Formalism.L2.Forms.mZ u (t.pt.til u a ha h1).z0) P
          (Formalism.L2.Forms.twYS t.ch C.forms u a (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl s)) →
      (t.pt.val u a ha).eW (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).PTw u a).lowerMap ψ) c =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u P) := by

  subst he
  obtain ⟨hW, hLv, hPd⟩ := hTw
  intro _ ψ c P _ hψ
  have hS := hC u
  have hPd' : I.StdP l Z l0 t.pt t.ptE := hPd
  have hW' : I.StdW l Z l0 t.forms := hW
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (sg_interlace (C.forms u).valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1' : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hPd'.eWz, hl', hPd'.z0 u a ha h1, mZ_std I l Z u hO hP (TC.z0 X u) (fun j => rfl)] at h
    refine h.trans ?_
    have h2 : (Formalism.L2.Forms.twYS t.ch C.forms u a (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl s).1 = s.1 := by
      simp only [Formalism.L2.Forms.twYS, Equiv.trans_apply, hW'.eY, Equiv.refl_symm, Equiv.refl_apply]
      rw [Formalism.L2.Forms.eYS_end _ _ _ (Or.inr rfl)]
      exact hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1']
    exact h
  have h4 : Formalism.L2.Ker.brTen (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hPd'.eW u a ha _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie
