module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataTies
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataKap
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.NchTieTr

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.BuDefQEta

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC.Gen

open Formalism.BasicNotions Formalism.MainNotions NumberField
open GlobalTheory.HeightCounting

structure Raw (D : D7) where
  η : ℕ → D.what₂.places.Pl → ℚ
  hη : ∀ j w, 0 ≤ η j w
  P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0
  hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P
  hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P

@[reducible] def Raw.rec' {D : D7} (Λ : Raw D) : D7 := setRaw D Λ.η Λ.hη Λ.P Λ.hZ Λ.hE

variable {D : D7} (Λ : Raw D)



@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ Λ.rec' := { L with }

@[reducible] def instTr {L : SizeData₂ D} (X : G.Inst D L) : G.Inst Λ.rec' (ledTr Λ L) := { X with }

@[reducible] def gatTr (x : GatTies D) : GatTies Λ.rec' := { x with }

@[reducible] def latTr (x : G.LatInst D) : G.LatInst Λ.rec' := { x with }

@[reducible] def cmpTr (x : LatCmp D) : LatCmp Λ.rec' := { x with }

@[reducible] def twTr (x : TwForms D) : TwForms Λ.rec' := { x with }

@[reducible] def thTr (x : ThetaX D) : ThetaX Λ.rec' := { x with }

@[reducible] def errTr (x : ErrX D) : ErrX Λ.rec' := { x with }

open DivX (md) in
@[reducible] def divTr (X : DivX D) : DivX Λ.rec' := { X with md := fun S κ p _ la z => { md X S κ p la z with } }
section Local

variable {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ)

theorem VV_tr : G.VV (instTr Λ X) K a b p = G.VV X K a b p := by
  have e1 : G.Cand _ (ledTr Λ L) K p = G.Cand D L K p := rfl
  have e2 : G.goodReps (instTr Λ X) p = G.goodReps X p := rfl
  have e3 : G.Sig (instTr Λ X) K a b p = G.Sig X K a b p := rfl
  unfold G.VV; rw [e1, e2, e3]; rfl

theorem tau_translate : G.tauP (instTr Λ X) K a b p = G.tauP X K a b p := by
  unfold G.tauP; rw [VV_tr]; rfl

theorem ioP_instTr : G.ioP (instTr Λ X) K a b p = G.ioP X K a b p := by
  unfold G.ioP; rw [VV_tr]; rfl

theorem gainP_instTr : G.gainP (instTr Λ X) K a b p j = G.gainP X K a b p j := by
  unfold G.gainP; rw [VV_tr]; rfl

theorem TTP_tr : G.TTP (instTr Λ X) K a b p = G.TTP X K a b p := by
  unfold G.TTP; rw [VV_tr]; rfl

theorem fills_tr (w : D.what₂.places.Pl) (H : G.ParametersFill X K w) : G.ParametersFill (instTr Λ X) K w :=
  ⟨H.1, H.2.1, H.2.2.1.trans (TTP_tr Λ X K _ _ _).symm,
    fun h1 h2 j hj => (H.2.2.2.1 h1 h2 j hj).trans (gainP_instTr Λ X K _ _ _ _).symm,
    H.2.2.2.2.1.trans (tau_translate Λ X K _ _ _).symm, H.2.2.2.2.2.1.trans (ioP_instTr Λ X K _ _ _).symm, H.2.2.2.2.2.2⟩

theorem NP_tr (Y : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    G.NP (instTr Λ X) (latTr Λ Y) K u w hg = G.NP X Y K u w hg := by
  have e0 : G.aL (ledTr Λ L) = G.aL L := rfl
  have e1 : G.bL (ledTr Λ L) = G.bL L := rfl
  have e2 : ∀ a b p t, G.Sv (instTr Λ X) K a b p t = G.Sv X K a b p t := fun _ _ _ _ => rfl
  unfold G.NP
  simp only [e0, e1, e2, VV_tr, tau_translate]
  rfl

end Local

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) (nch : NChoice Λ.rec') (tie : NChTie Λ.rec' nch) (xd : ThData Λ.rec')
    (p0 : BaseLevelRowSide Λ.rec') (rr0 : p0.s.RRDef) (amb : AmbForm Λ.rec' (RowSide.sharp Λ.rec')) (amb0 : AmbForm Λ.rec' p0.s)
    (ks : kapSharp Λ.rec' = kapSharp D) :
    Extra Λ.rec' (ledTr Λ L) (gatTr Λ gatT) (instTr Λ Gx) (latTr Λ Gy) K (divTr Λ X) cX where
  lev := ex.lev
  th := thTr Λ ex.th
  th_io := ex.th_io
  cmp := cmpTr Λ ex.cmp
  lat := ⟨ex.lat.vram, fun u w hg hv x => by
    erw [NP_tr]; exact ex.lat.served u w hg (by rw [← VV_tr Λ]; exact hv) x, ex.lat.atT⟩
  tw := twTr Λ ex.tw
  ker := fun u w g => { ex.ker u w g with }
  ep_def := ex.ep_def
  ep_tie := ex.ep_tie
  kapI_def := ex.kapI_def
  fills_all := ex.fills_all
  nu_unserved := fun u w h1 h2 => ex.nu_unserved u w h1 (by rw [← VV_tr Λ]; exact h2)
  idx := { ex.idx with }
  kap_def := ex.kap_def
  lam_def := ex.lam_def
  kapR_def := ex.kapR_def.trans ks.symm
  errX := errTr Λ ex.errX
  err := { ex.err with }
  nch := nch
  nch_tie := tie
  xd := xd
  p0 := p0
  rationalRoots_def := rr0
  amb := amb
  amb0 := amb0
  fdef := ex.fdef
  duStar_def := ex.duStar_def
  Dstar_def := ex.Dstar_def
  gauge := ex.gauge
  gauge_def := ex.gauge_def

@[reducible] def parTr {L : SizeData₂ D} (P : ParameterChoice' D L) : ParameterChoice' Λ.rec' (ledTr Λ L) := { P with }

@[reducible] def parTTr {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : ParamsT Λ.rec' (ledTr Λ L) (parTr Λ P) := { T with }

set_option smartUnfolding false in
theorem buDefQ_eta (h : Rows.BuDefQ D.what₂) : Rows.BuDefQ (rowsEta D.what₂ Λ.η Λ.hη) := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).sec D.what₂.mu0 = D.what₂.sec D.what₂.mu0 := by
    first
      | rfl
      | with_unfolding_all rfl
  intro u φ x
  have := h u φ x
  rw [← e] at this
  exact this

theorem tiesTr (h : Ties D) (k : TwCoverPair Λ.rec') : Ties Λ.rec' := { h with bu_def := buDefQ_eta Λ h.bu_def, tw_cover := k }

set_option smartUnfolding false in
theorem rrDefTr (h : DV.RRDef D) : DV.RRDef Λ.rec' := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).RRset = D.what₂.RRset := by
    first
      | rfl
      | with_unfolding_all rfl
  intro x
  have := h x
  rw [← e] at this
  exact this

end UpperTheory.GalC.Gen
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.KapSharpTr

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)



@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (cut D Λ) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr Λ S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f => f.comp (S.io μ j)) ih

theorem iota_tr (μ : D.what₂.Tup) : (sideTr Λ S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]; rfl

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr Λ S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr Λ S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr Λ S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr Λ S _) (Qsp_tr Λ S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr Λ S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr Λ S).RRDef := by
  have e : (sideTr Λ S).RRset = S.RRset := funext (RRset_tr Λ S)
  unfold RowSide.RRDef; rw [e]; exact H

end Side

theorem kapSharp_tr : kapSharp (cut D Λ) = kapSharp D := kapOf_tr Λ (RowSide.sharp D) _

def ambTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (x : AmbForm D S) :
    AmbForm (cut D Λ) (sideTr Λ S) := { x with }

end UpperTheory.GalC
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExtraTr

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (c : CutD D)

def raw : Gen.Raw D :=
  ⟨(layCut D c).eta, (layCut D c).eta_nonneg, (layCut D c).reEta _ (layCut D c).eta_nonneg, (layerCut_admissible D c).reEta _ _,
    (layCut D c).etaOk_reEta⟩

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (cut D c) := Gen.ledTr (raw c) L

theorem tiesTr (h : Ties D) : Ties (raw c).rec' := Gen.tiesTr (raw c) h h.tw_cover



def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (raw c).rec' (Gen.ledTr (raw c) L) (Gen.gatTr (raw c) gatT) (Gen.instTr (raw c) Gx) (Gen.latTr (raw c) Gy) K
      (Gen.divTr (raw c) X) cX :=
  Gen.extraTr (raw c) ex (nchTr c ex.nch) (nchTie_tr c ex.nch_tie) (xdTr c ex.xd)
    (show BaseLevelRowSide (cut D c) from ⟨sideTr c ex.p0.s⟩) (rrDef_tr c _ ex.rationalRoots_def) (ambTr c ex.amb) (ambTr c ex.amb0) (kapSharp_tr c)

end UpperTheory.GalC
end
end
end
