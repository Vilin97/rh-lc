module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move



set_option maxRecDepth 100000 in
theorem heckeTie_of_same {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hsp : HEq D.sp D'.sp) {ρ : Setup X} {ρ' : Setup X'} {i : X.Tw} {i' : X'.Tw} (hi : HEq i i')
    {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') {b : Bool}
    (hmu : HEq (ρ.B i j b).mu (ρ'.B i' j' b).mu) (hlev : HEq (ρ.levK i j b) (ρ'.levK i' j' b))
    (r : Rd ρ Y i j b) (r' : Rd ρ' Y' i' j' b)
    (hR : ∀ (f : Y.Fm i ((j : ℕ) + 1) b) (f' : Y'.Fm i' ((j' : ℕ) + 1) b), HEq f f' → HEq (r' f') (r f))
    (ht : HeckeTie r) : HeckeTie r' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3 hsp
  subst a1; subst a2; subst a3; subst hsp
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hi
  obtain rfl : j = j' := Fin.ext hj
  have e : ∀ x, r' x = r x := fun x => eq_of_heq (hR x x HEq.rfl)
  have hmu' : (ρ'.B i j b).mu = (ρ.B i j b).mu := eq_of_heq hmu.symm
  have hlev' : ρ'.levK i j b = ρ.levK i j b := eq_of_heq hlev.symm
  have hk : ∀ k P R z F, ρ'.hecke i j b k P R z F = ρ.hecke i j b k P R z F := fun k P R z F => by
    funext x
    rw [Setup.hecke_apply, Setup.hecke_apply, hmu']
  have hd : ∀ k P α R z, ρ'.IsHeckeDatum i j b k P α R z ↔ ρ.IsHeckeDatum i j b k P α R z := fun k P α R z =>
    ⟨fun d => ⟨d.1, hlev' ▸ d.2, d.3⟩, fun d => ⟨d.1, hlev'.symm ▸ d.2, d.3⟩⟩
  have ha : ∀ k P f g, HeckeAt r' k P f g ↔ HeckeAt r k P f g := fun k P f g =>
    ⟨fun hg α R z d => by have := hg α R z ((hd k P α R z).2 d); rwa [e, e, hk] at this,
      fun hg α R z d => by rw [e, e, hk]; exact hg α R z ((hd k P α R z).1 d)⟩
  intro k P hkP f hf
  exact (ha k P f _).2 (ht k P hkP f (by obtain ⟨g, hg⟩ := hf; exact ⟨g, (ha k P f g).1 hg⟩))

theorem heckeTie_move_of_pin : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw},
    (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) (b : Bool),
      HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b)) →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) := by
  intro D D' ι e h ρ ρ' hB rd rd' hr i i' hi j b ht
  have hR : ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (f' : D'.nexp.Fm i' ((h.cm j : ℕ) + 1) b), HEq f f' →
      HEq (rd' i' (h.cm j) b f') (rd i j b f) := fun f f' hf => by
    have h1 : h.fmCast hi ((j : ℕ) + 1) b f = f' := eq_of_heq ((h.fmCast_heq hi _ b f).trans hf)
    rw [← h1]
    exact hr i i' hi j b f
  exact heckeTie_of_same h.gal h.set h.frm h.sp hi (h.cm_val j).symm (hB i i' hi j b).1 (hB i i' hi j b).2
    (rd i j b) (rd' i' (h.cm j) b) hR ht



theorem SameData.mu_levK {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameData ρ ρ') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i')
    (j : Fin D.R.m) (b : Bool) :
    HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b) := by
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  cases hi
  cases (Fin.ext hj : j = j')
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heckeTie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameData ρ ρ' →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) :=
  fun h _ _ hs => heckeTie_move_of_pin h (hs.mu_levK h)

end GlobalTheory.TwInputs.Move

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem isExtremalVector_of_realSideBaseChange : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι), (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _) := by
  intro D D' ι e h X X' m _ j
  exact X'.geo.fw.hv₀ j _

end GlobalTheory.TwInputs.Move
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr



set_option maxRecDepth 100000 in
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  have nOm := h.cp.gal.Om
  have ninstOm := h.cp.gal.instOm
  have nalgOm := h.cp.gal.algOm
  have nplOm := h.cp.gal.plOm
  have nPlG := h.cp.gal.PlG
  have hR := h.cp.gal.R
  have hhost := h.cp.gal.host
  have hTau := h.cp.Tau
  have heTau := h.cp.eTau
  have hhc := h.cp.hc
  have hinW1 := h.cp.inW1
  have hemb0 := h.cp.emb0
  have hTw := h.cp.set.Tw
  obtain ⟨xcc, _, _, _, _, xalgO0, xtopO0, _, _, _, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, _, xhEig, _, _, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.cp.set
  have hjL := h.jL
  have hs2 := h.s2
  have hlamG := h.lamG
  have hXv := h.Xv
  have hqs := h.qs
  have hl := h.cp.set.l
  have hO0 := h.cp.set.O0
  have hcrO0 := h.cp.set.crO0
  have hab := h.cp.set.abelian₂
  have hsideL := h.cp.set.sideL
  have hO := h.cp.set.O
  have hcrO := h.cp.set.crO
  have halgO := h.cp.set.algO
  have hS0 := h.cp.set.S0
  cases D; cases D'
  dsimp only at hR hhost
  subst hR; subst hhost
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  rename NData _ _ _ => nd1; cases nd1
  rename NData _ _ _ => nd2; cases nd2
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => n1; cases n1
  rename NTw _ _ _ _ _ => n2; cases n2
  dsimp only at xcc
  subst xcc
  dsimp only at hTw hl hO0 hcrO0 hab hsideL hO hcrO halgO hS0
  subst hTw; subst hl; subst hO0; subst hcrO0; subst hab; subst hsideL; subst hO; subst hcrO; subst hS0
  dsimp only at xalgO0 xtopO0 xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xhEig xRCG xgrpRCG xfinRCG xart xth hjL hs2 hlamG hXv hqs halgO
  subst xalgO0; subst xtopO0; subst halgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xhEig; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hjL; subst hs2; subst hlamG; subst hXv; subst hqs
  cases C; cases cf'  
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem exportTie_move (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S)
    (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (Z : ExportTie YS X.geo.v₀) :
    ∃ Z' : ExportTie (Forms.tie h m YS hsup) X'.geo.v₀, SameSetup Z.ρ Z'.ρ ∧
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
        Z'.ν i' (h.cm j) b = Z.ν i j b ∧ HEq (Z.tie i j b).rdV (Z'.tie i' (h.cm j) b).rdV := by
  obtain ⟨ρ', hs, hg, hp⟩ := setup_move h m Z.ρ Z.good Z.pin
  have hrd := Forms.rdRel_move h m YS hsup Z.ρ ρ' hs Z.good hg
  have hm : D'.R.m = D.R.m := (congrArg Ranks.m h.gal.R).symm
  let ν' : D'.ntw.Tw → Fin D'.R.m → Bool → ℂ := fun i' j' b => Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm j') b
  have hν : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b, ν' i' (h.cm j) b = Z.ν i j b := by
    intro i i' hi j b
    have e1 : cast h.Tw_eq.symm i' = i := eq_of_heq ((cast_heq _ _).trans hi.symm)
    have e2 : Fin.cast hm (h.cm j) = j := Fin.ext rfl
    change Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm (h.cm j)) b = _
    rw [e1, e2]
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ h.cm j = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast hm j', cast_heq _ _, Fin.ext rfl⟩
  have hrdZ : RdRel h (fun i j b => realRd YS X.geo.v₀ Z.good i j b (Z.ν i j b))
      (fun i j b => realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i j b (ν' i j b)) := by
    intro i i' hi j b f
    have := hrd (Z.ν i j b) i i' hi j b f
    change HEq (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' (h.cm j) b (ν' i' (h.cm j) b) _) _
    rw [hν i i' hi j b]
    exact this
  obtain ⟨T', hT'⟩ := TieUp.tie_move h hs Z.good hg _ _ hrdZ Z.tie
  have hv := isExtremalVector_of_realSideBaseChange h m Z.vec
  have hsc : ∀ i' j' b, IsScalar (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    rw [hν i i' hi j b]
    exact scalar_move h m hs Z.good hg Z.pin hp Z.vec hv hrd i i' hi j b _ (Z.scalar i j b)
  have hhk : ∀ i' j' b, HeckeTie (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b)) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    exact heckeTie_move h hs _ _ hrdZ i i' hi j b (Z.hecke i j b)
  exact ⟨ExportTie.mk ρ' hg hp hv ν' hsc T' hhk (GlobalTheory.UnivCharCopy.isUnivChar_copy h Z.univ), hs,
    fun i i' hi j b => ⟨hν i i' hi j b, hT' i i' hi j b⟩⟩

theorem serAt_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S) {Xe : NExpTied D} {Xe' : NExpTied D'} (hX : ExpMove Xe Xe')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {cf : CharFrame D} {cf' : CharFrame D'}
    (hcf : SameFrame cf cf') {Pq Pq'} (hPq : HEq Pq Pq') (Z : SerAt YS X.geo.v₀ Xe PV cf Pq) :
    Nonempty (SerAt (Forms.tie h.cp m YS Z.sup) X'.geo.v₀ Xe' PV' cf' Pq') := by
  obtain ⟨Z', hs, hr⟩ := exportTie_move h.cp m YS Z.sup Z.ex
  obtain ⟨lam, l1, l2, l3, l4, l5⟩ := LamCopy.lam_copy h hcf ⟨Z.lam, Z.lam_ok, Z.lam_teich, Z.lam_C, Z.lam_q, Z.lam_tie⟩
  refine ⟨{ ex := Z'
            bad := (low_copy h.cp).2.1 _ _ hs.bad Z.bad
            ch := (pq_copy h.cp Pq Pq' hPq).1 _ _ hs.ch Z.ch
            join := fun i' j' b k Q' ψ' hA' hT' => ?_
            sup := sup_move h.cp m YS Z.sup
            off := (low_copy h.cp).2.2 Z.off
            lam := lam
            lam_ok := l1
            lam_teich := l2
            lam_C := l3
            lam_q := l4
            lam_tie := l5 }⟩
  obtain ⟨j, rfl⟩ : ∃ j, h.cp.cm j = j' := ⟨⟨j', lt_m h.cp j'.2⟩, rfl⟩
  obtain ⟨i, Q, ψ, hi, hQ, hψ, hT, e1, e2, e3, e4⟩ := join_copy h.cp i' j (h.cp.cm j) rfl b k Q' ψ' hT'
  obtain ⟨e5, e6⟩ := e4 _ _ hs.ek
  obtain ⟨hA, -, -, hR⟩ := hX i i' hi ((j : ℕ) + 1) b k Q Q' hQ ψ ψ' hψ (Nat.le_add_left _ _) j.2 (h.cp.cm j).2 hA'
  exact hR _ _ e5 _ _ e1 e2 e3 _ _ (e6 _ _ (hr i i' hi j b).2 _ _ (keepsMat_heq h.cp _ _ hp hp' j (h.cp.cm j) rfl))
    (Z.join i j b k Q ψ hA hT)

theorem series_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι)
    (g₀ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) (g₁ : GlobalTheory.RealGeo.GeoHalf X'.core X'.R.toRealDat fun _ => 1)
    {kKs hk} (kKs' hk') (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hl : LowIn D) {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
    {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL') {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c)
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : SameFrame cf cf') (s : CharSide D cf) (s' : CharSide D' cf')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {Pq Pq'} (hPq : HEq Pq Pq')
    {Xe : NExpTied D} (hq : PqLaw Xe Pq) (hτ : TauTrue Xe) (Z : SerAt YS g₀.v₀ Xe PV cf Pq) :
    ∃ (YS' : NX.NExpRealS X'.R X'.cG (NX.ratDatR X'.R X'.cG kKs' hk')) (Xe' : NExpTied D'), PqLaw Xe' Pq' ∧
      HkLaw D' (NX.ratDatR X'.R X'.cG kKs' hk') YS'.eF hL' hs' c' ∧ (∀ i x, HEq ((YS'.fi i).e x) x) ∧
      Nonempty (SerAt YS' g₁.v₀ Xe' PV' cf' Pq') ∧ TauTrue Xe' := by
  obtain rfl : kKs' = m.kKsOf (e := e) YS (NX.idxOf D 0) :=
    RingHom.ext fun x => Subtype.ext ((hk' x).trans (m.kKsOf_spec h.cp YS _ x).symm)
  obtain ⟨Xe', ht, hX⟩ := GlobalTheory.HeightCounting.ExpCopy.expTied_copy h hcf s s' Xe
  obtain ⟨Z₁⟩ := GlobalTheory.SerVec.serAt_vec X g₀ X.geo YS _ _ _ _ Z
  obtain ⟨Z₂⟩ := serAt_move h m YS hX hp hp' hcf hPq Z₁
  exact ⟨Forms.tie h.cp m YS Z₁.sup, Xe', pqLaw_move h.cp hX hPq hq,
    hkLaw_move h.cp m YS hfi hl ((low_copy h.cp).1 hl) hSb hSb' H H' Z₁.sup hs' hc L, fun i x => fiOfEq_heq X' _ x,
    GlobalTheory.SerVec.serAt_vec X' X'.geo g₁ _ _ _ _ _ Z₂, ht hτ⟩

end GlobalTheory.HeightCounting.SerCarry

end
end
end
