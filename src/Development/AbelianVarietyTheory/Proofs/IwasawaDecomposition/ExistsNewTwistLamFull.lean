module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharacterEqLadicHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongrStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarP

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr



namespace GlobalTheory.HeightCounting.SerCopy

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev DN (x : St P) (N : TwNew (Dof x)) : D7 := (w.st (oTw x N).Z).toD7

def oth (x : St P) (N : TwNew (Dof x)) : Oth (B := B) (C := w.C) (P.q.W x.o.η x.o.hη) := ⟨x.o.V, x.o.S, nTw x N, x.o.G⟩

variable {x : St P}

def baN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m} (X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)) :
    ExportSeries.Base (Vc (DN x N') ((j))) (Wc (DN x N') ((j))) :=
  (@baT B (@ColW.C B f T w) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N)) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N')) (Vc (@DN K B f T w P x N) j) (Wc (@DN K B f T w P x N) j) X)


theorem isNormN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m}
    {X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)} {ν : ℂ} (h : IsNorm (D := DN x N) (datTw x N).R (datTw x N).geo.v₀ X ν) :
    IsNorm (D := DN x N') (datTw x N').R (datTw x N').geo.v₀ (j := (j)) (@baN K B f T w P x N N' j X) ν := by
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in
  · obtain ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
    refine ⟨h0, c, ⟨g, c0R, c0L, ?_, u, hu, hh⟩, hn⟩
    with_unfolding_all
      -- Infer the family data from the source proof before comparing with the target.
      have hF' := @famTie_imp B w.C (oTw x N).Z (oTw x N').Z
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g c0R c0L hF
      exact hF'

variable {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (datTw x N₁).core.Q.c.F, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {YS : NExpRealS (datTw x N₁).R (datTw x N₁).cG (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk)} {X : NExpTied (DN x N₁)} {hF Pq}
  (p : PreTie YS (datTw x N₁).geo.v₀ X hF Pq)

def nP : TwNew (Dof x) := ⟨N₁.tw, PreTie.ex (D := DN x N₁) (Ks := (datTw x N₁).core.Q.c.F) p, N₁.h0, PreTie.nth (D := DN x N₁) (Ks := (datTw x N₁).core.Q.c.F) p, N₁.br, N₁.hbr⟩

def kP : (datTw x (nP p)).core.Q.c.F →+* ↥(DN x (nP p)).LL0 := (kKs)

theorem hkP : ∀ y, ((kP p y : ↥(DN x (nP p)).LL0) : (DN x (nP p)).what₂.LL) =
    algebraMap (datTw x (nP p)).core.Q.c.F (DN x (nP p)).what₂.LL y := (hk)

abbrev sP : RatDat (DN x (nP p)).ntw := ratDatR (datTw x (nP p)).R (datTw x (nP p)).cG (kP p) (hkP p)

def ysP : NExpRealS (datTw x (nP p)).R (datTw x (nP p)).cG (sP p) where
  fi := (YS.fi)
  geq := (YS.geq)
  rho := (YS.rho)
  chi := (YS.chi)
  eF := (YS.eF)
  bsup := (YS.bsup)
  act := (YS.act)

def rhoP : Setup (DN x (nP p)).ntw :=
  (by with_unfolding_all exact ((@seT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ))) : _))

theorem goodP : (rhoP p).Good := by
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in
  with_unfolding_all
    exact @seGood B w.C _ (oth x N₁) (oth x (nP p)) (DN x N₁).nd (DN x N₁).ntw p.ρ p.good

theorem pinP : RealPin (datTw x (nP p)).R (datTw x (nP p)).cG (rhoP p) := by
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in
  exact ⟨p.pin.psi, p.pin.inf, p.pin.cartT, p.pin.onbS, p.pin.onbT, p.pin.latS,
    p.pin.latT, p.pin.frS, p.pin.frT, p.pin.vac, p.pin.Pg, p.pin.grp, p.pin.mu0,
    p.pin.eta, p.pin.delta, p.pin.deltaPl, p.pin.ap, p.pin.am⟩

theorem ratP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    SeriesTie.Rat (goodP p) (realRd (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b ν) ↔
      SeriesTie.Rat p.good (realRd YS (datTw x N₁).geo.v₀ p.good i j b ν) := by
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in
  with_unfolding_all
    let rd := realRd YS (datTw x N₁).geo.v₀ p.good i j b ν
    exact ⟨@ratT' B w.C _ (oth x N₁) (oth x (nP p)) (DN x N₁).nd (DN x N₁).ntw
        p.ρ i j b p.ex rd p.good,
      @ratT B w.C _ (oth x N₁) (oth x (nP p)) (DN x N₁).nd (DN x N₁).ntw
        p.ρ i j b p.ex rd p.good⟩

theorem normP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    IsNorm (datTw x (nP p)).R (datTw x (nP p)).geo.v₀ ((rhoP p).B ((i)) ((j)) b) ν ↔
      IsNorm (datTw x N₁).R (datTw x N₁).geo.v₀ (p.ρ.B i j b) ν := by
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in
  with_unfolding_all
    exact ⟨@isNormN K B f T w P x (nP p) N₁ j ((rhoP p).B i j b) ν,
      @isNormN K B f T w P x N₁ (nP p) j (p.ρ.B i j b) ν⟩

theorem scalarP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) :
    IsScalar (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b (p.ν i j b) :=
  ⟨(p.scalar i j b).ne, fun h => (normP p i j b _).2 ((p.scalar i j b).norm (h.imp fun ν => (normP p i j b ν).1)),
    fun h => (ratP p i j b _).2 ((p.scalar i j b).rat (h.imp fun ν h' => ⟨(normP p i j b ν).1 h'.1, (ratP p i j b ν).1 h'.2⟩))⟩

def exP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) : ExportTie (ysP p) (datTw x (nP p)).geo.v₀ where
  ρ := rhoP p
  good := goodP p
  pin := pinP p
  vec := (p.vec)
  ν := (p.ν)
  scalar := fun i j b => (scalarP p i j b)
  tie := fun i j b => (by with_unfolding_all exact ((@cellT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) ((p.good))
      (((p.tie ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  hecke := fun i j b => (by with_unfolding_all exact ((@heckeTieT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i))
      ((j)) b ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b))))
      (((p.hecke ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  univ := (hu)

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
def expP : NExpTied (DN x (nP p)) :=
  -- Use the fieldwise construction of `keepExp` at the stage produced by `nP`.
  { X with
    acgWt := X.acgWt
    modWt := X.modWt
    fdWt := X.fdWt
    thU_empty := fun i j b M d hj hj' => p.hU i j b M d hj hj'
    mtV := fun i j b k Q ψ hj hj' hA => by
      letI : AddCommGroup (X.Wt i j b) := X.acgWt i j b
      letI : Module (FractionRing ((DN x (nP p)).ntw.O i)) (X.Wt i j b) := X.modWt i j b
      exact { X.mtV i j b k Q ψ hj hj' hA with } }

def pvP (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) (j : Fin (DN x N₁).R.m) :
    principalLevelFrame.RowPsi (Vc (DN x N₁) j) (DN x N₁).R.nV :=
  ⟨((PV j).ψ), ((PV j).inj), ((PV j).into), ((PV j).onto)⟩

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
def serP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (hs : ∀ i j b h1 h2 (y : (DN x N₁).nexp.Fm i j b), y ∈ (DN x N₁).nexp.Bsup i j b ↔
      YS.eF i j b h1 h2 y ∈ Bsup (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) i j b)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j)) {cf : CharFrame (DN x (nP p))} (Z : GlobalTheory.LamTie.LamDat (DN x (nP p)))
    (hZ : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z) :
    SerAt (ysP p) (datTw x (nP p)).geo.v₀ (expP p) PV cf ((Pq)) where
  ex := exP p hu
  bad := (p.bad)
  ch := (p.ch)
  join := by
    intro i j b k Q ψ hA hOK
    have hjoin := p.join (pvP p PV) (fun j => hPV j) i j b k Q ψ hA hOK
    with_unfolding_all exact hjoin
  sup := (hs)
  off := (ho)
  lam := Z
  lam_ok := hZ.1
  lam_teich := hZ.2.1
  lam_C := hZ.2.2.1
  lam_q := hZ.2.2.2.1
  lam_tie := hZ.2.2.2.2

end GlobalTheory.HeightCounting.SerCopy

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTauFamily

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)

theorem GlobalTheory.TwInputs.tauG_read (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (i : D.ntw.Tw) (b : Bool) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (x : (ZMod (D.host.g k))ˣ)
    (u : 𝓞 D.host.E) (hu0 : (u : D.host.E) ≠ 0)
    (hxu0 : (((x : ZMod (D.host.g k)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D ⟨k, v⟩).asIdeal)
    (hl0 : NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i)) :
    (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) ^ (D.host.g k - 1) = 1 ∧
    ∀ y : ↥D.LL0, embLL0 D y = (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) →
      ((Bs.exp.tauG i (j.1 + 1) b ⟨k, v⟩ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b y := by
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  obtain ⟨n, hn⟩ := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ j
  have hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := hl0
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgw
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg2 := hgp.two_le
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu : u ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 : (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
      have := (D.naut.plGw k v).asIdeal.add_mem hxu0 h
      rwa [sub_add_cancel] at this
    obtain ⟨a, c, hac⟩ : IsCoprime (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
      (ZMod.val_coe_unit_coprime x).cast
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hac]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hgw)
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap D.host.E D.nd.Om (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E))
    (show 0 < normV (D.naut.plGw k v) - 1 by omega)
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw _ hgw hspl.2.1 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  have hTR : NX.TameRep (D.naut.plGw k v) 1 σ u :=
    ⟨_, hAw, hσI, _, π, hgw, hspl.2.1, hπ, by simpa using hσval⟩
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase] at e1
  change _ = (((cf.mu0 j).loc _ _ * (cf.delAt (D.ntw.l i)).loc _ _ : ℂˣ) : ℂ) at e1
  rw [hdel _ hxu, mul_one] at e1
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hex : ∃ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, NX.TameRep (D.naut.plGw k v) 1 s u := ⟨σ, hTR⟩
  have e2 : NX.tameVal (D.ntw.chi1 i (j.1 + 1) b) (D.naut.plGw k v) 1 u = D.ntw.chi1 i (j.1 + 1) b σ := by
    unfold NX.tameVal
    rw [dif_pos hex]
    refine GlobalTheory.T.tameChar_eq_of_tameRep_congr (D.naut.plGw k v) (D.ntw.twistBaseCoefficientRing_isAdic i) _ (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b) (by omega) hm
      (fun A hA s hs => ?_) _ _ u u hex.choose_spec hTR (by rw [sub_self]; exact zero_mem _)
    rw [hN]
    exact D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl A hA s hs
  have e3 := Bs.exp.tau_galois_first_character i (j.1 + 1) b ⟨k, v⟩ x u (by omega) (by omega) hl0 hxu0
  rw [Bs.exp.sgnG_one, Bs.exp.sgnT_one, one_mul] at e3
  have e1' : ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) b σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) := e1
  have ht : (D.ntw.chi1 i (j.1 + 1) b σ) ^ (D.host.g k - 1) = 1 :=
    D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw σ hσI
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← e1', ← map_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ht]
    simp
  · have e4 : GlobalTheory.Triple.embSide D.ntw i b y =
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) b σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      apply ρ.κ.injective
      apply ρ.ι.injective
      rw [ρ.read, hy, e1']
    have e5 : sideEmb D.ntw i b y = (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) (GlobalTheory.Triple.embSide D.ntw i b y) := by
      cases b <;> rfl
    rw [e5, e4, ← e2]
    refine e3.trans ?_
    simp only [IsFractionRing.map, IsLocalization.map_eq]
    rfl

theorem GlobalTheory.TwInputs.exists_tau_family : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∃ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV hroot
  have key : ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ t : (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
      ∀ i b x, NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
        ((Bs.exp.tauG i (j.1 + 1) b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
          sideEmb D.ntw i b ((t x : (↥D.LL0)ˣ) : ↥D.LL0) := by
    rintro j ⟨k, v⟩
    have hgp : (D.host.g k).Prime := D.host.g_prime k
    haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
    obtain ⟨p, hpg, hp⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨⟨w, hw⟩⟩ := Formalism.BasicNotions.Examples₂.PlOver.plNe D p
    obtain ⟨i₀, hi, -⟩ := Bs.cover w
    have hk : D.ntw.l i₀ ≠ D.host.g k := by rw [hi, hw]; omega
    have hl₀ : NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i₀) := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
    have hy : ∀ x : (ZMod (D.host.g k))ˣ, ∃ y : ↥D.LL0, ∀ i b, NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i) →
        ((Bs.exp.tauG i (j.1 + 1) b ⟨k, v⟩ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
          sideEmb D.ntw i b y := by
      intro x
      have hx0 : (x : ZMod (D.host.g k)).val ≠ 0 := by
        rw [Ne, ZMod.val_eq_zero]
        exact x.ne_zero
      have hu0 : ((((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
        exact_mod_cast hx0
      have hxu : (((x : ZMod (D.host.g k)).val : 𝓞 D.host.E) - ((x : ZMod (D.host.g k)).val : 𝓞 D.host.E)) ∈
          (NX.pG D ⟨k, v⟩).asIdeal := by
        rw [sub_self]; exact zero_mem _
      have h0 := (GlobalTheory.TwInputs.tauG_read hGAR D cf Rw low Pq S hL eig θ Bs hV i₀ true j k v x _ hu0 hxu hl₀).1
      obtain ⟨y, hy⟩ := hroot k _ (by rw [mul_comm, pow_mul, h0, one_pow])
      exact ⟨y, fun i b hl =>
        (GlobalTheory.TwInputs.tauG_read hGAR D cf Rw low Pq S hL eig θ Bs hV i b j k v x _ hu0 hxu hl).2 y hy⟩
    choose Y hY using hy
    have hinj := (sideEmb D.ntw i₀ true).injective
    let f : (ZMod (D.host.g k))ˣ →* ↥D.LL0 :=
      { toFun := Y
        map_one' := hinj (by rw [← hY 1 i₀ true hl₀, map_one, map_one, Units.val_one])
        map_mul' := fun a c => hinj (by
          rw [map_mul, ← hY _ i₀ true hl₀, ← hY _ i₀ true hl₀, ← hY _ i₀ true hl₀, map_mul, Units.val_mul]) }
    exact ⟨f.toHomUnits, fun i b x hl => hY x i b hl⟩
  choose t ht using key
  refine ⟨fun j kv => if h : j - 1 < D.R.m then t ⟨j - 1, h⟩ kv else 1, ?_⟩
  intro i j b kv x h1 h2 hl
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h : j' + 1 - 1 < D.R.m := by omega
  simp only [dif_pos h]
  exact ht ⟨j', h⟩ kv i b x hl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr



namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

section Install

variable {x : St P} {N₁ : TwNew (Dof x)}
  {kKs : (Up.datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (Up.datTw x N₁).core.Q.c.F,
    ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) =
      algebraMap (Up.datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host}
  {hf : ∀ j, ℕ → PlE (DN x N₁).host →
    Module.End (DN x N₁).what₂.LL ((ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk).WL j)}
  {eig : ℕ → (DN x N₁).what₂.FT → ℕ → PlE (DN x N₁).host → ↥(DN x N₁).LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod ((DN x N₁).host.g kk)) →* (↥(DN x N₁).LL0)ˣ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq
    (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk) hf eig θ}
  {hF : (DN x N₁).host.F = maximalRealSubfield (DN x N₁).host.E}

abbrev kwP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) : TwNew (DN x N₁) :=
  keepTw (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) :
    SideB (kwP p).toD7 ((kwP p).cf cf) ((kwP p).row Rw)
      (lowAll (DN x (SerCopy.nP p))) Pq
      ((kwP p).rat (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk)) hf eig θ := by
    exact keepSideB (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi
      p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs

end Install


end GlobalTheory.HeightCounting.SerCopy

end
end
end
