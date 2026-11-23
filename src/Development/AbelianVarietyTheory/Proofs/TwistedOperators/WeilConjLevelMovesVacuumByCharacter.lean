module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusProdLocalUnitIdelesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPairStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.TopLevelInv

theorem det_kapAt_val {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (mt (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).det) := by
  unfold kapAt GlobalTheory.FunObj.inBasis
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.SplitFlip.gdet, GlobalTheory.StepData.det_reGL]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨X, hX⟩ : ∃ X, X = (MulAut.conj (S.βp (j + 1))⁻¹) ((finG (G.V (.top (j + 1)))) k) := ⟨_, rfl⟩
  rw [← hX]
  refine ((RingHom.map_det (StdFrames.cpt w) X.val).symm : _).trans (congrArg _ ?_)
  rw [hX, MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, inv_inv, mul_right_comm, ← det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul]
  show ((Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).val).det = _
  rw [GlobalTheory.VecInv.finE_val, RingHom.map_det]
  rfl




theorem detAt_conjPt_eq_prod {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} (_ht : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1)))
    (e : AE D) (hI : IsIdemSum e (locPl G t)) :
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  classical
  have he2 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI).idem
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hI
  have hcomp : ∀ Q, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = if Q ∈ locPl G t then 1 else 0 := by
    intro Q
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hI

    rw [hsum, map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) Q)]
    split_ifs with hQ
    · rw [Finset.sum_eq_single Q (fun P hP hPQ => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
        (fun h => absurd hQ h)]
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
    · exact Finset.sum_eq_zero fun P hP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))
  have hloc : ∀ (w Q : Pl D.host.E) (y : (Kw w)ˣ),
      GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
    intro w Q y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  have hdet : (mt (G.V (.top (j + 1))) (conjPt S j k)).det = (mt (G.V (.top (j + 1))) (k : GA D _)).det := by
    unfold Formalism.L2.Theta.mt
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_right_comm, inv_mul_cancel, one_mul]
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Units.coe_prod, hdet]
  apply GlobalTheory.FunObj.ae_ext
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero, map_prod]
    exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _).symm
  · intro Q
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, map_prod, hcomp, hloc]
    by_cases hQ : Q ∈ locPl G t
    · rw [if_pos hQ, one_mul, sub_self, add_zero, Finset.prod_eq_single ⟨Q, hQ⟩]
      · rw [GlobalTheory.LFun.finSingle_self, det_kapAt_val]
      · intro b _ hb
        exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hQ, zero_mul, zero_add, sub_zero]
      exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _).symm

end GlobalTheory.TopLevelInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (e : AE D),
    IsIdemSum e (locPl G t) →
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  first | exact @GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | exact GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | (intros; apply GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.IdemSumF

theorem exists_idem_below : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e :=
  fun he => Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_eps he

end GlobalTheory.IdemSumF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e := by
  first | exact @GlobalTheory.IdemSumF.exists_idem_below | exact GlobalTheory.IdemSumF.exists_idem_below | (intros; apply GlobalTheory.IdemSumF.exists_idem_below <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem chrS_top_prod_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  intro D T L sc G t μ₀ hL j hj y
  have hrank : (G.pS (.top t j)).rank = rankX D j :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).rank
  have hchr : G.chrS (.top t j) = L.mu t (j + 1) := by
    rw [GridData.chrS, hrank]
    simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D j)]
  have hE : ChrEq (L.mu t (j + 1)) (muBase L (j + 1) * L.xiH t) := by
    have h1 : muBase L (j + 1) = L.C.mu0 ⟨j, by omega⟩ := dif_pos (by omega)
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, by omega⟩) (hL.xi t)
  rw [hchr, map_prod]
  rw [show ∀ (s : Finset (locPl G t)) (f : locPl G t → Circle), ((∏ w ∈ s, f w : Circle) : ℂ) = ∏ w ∈ s, (f w : ℂ) from
    fun s f => map_prod Circle.coeHom f s]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact congrArg (fun f => ((f (y w) : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

end GlobalTheory.TopLevelInv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdelesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.topPairSourceChar_prod_localIdeles : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TopLevelInv.chrS_top_prod_locIdele | exact GlobalTheory.TopLevelInv.chrS_top_prod_locIdele | (intros; apply GlobalTheory.TopLevelInv.chrS_top_prod_locIdele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacter

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem omega_conj_vac_low: ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  change W.om (.top t j) (1, conjPt S j k) (S.Z.vac (.top t j)) = _ • Tm fun x => halfInd e (stdLatO S (.top t j))
    (actO _ _ 1⁻¹ (conjPt S j k)⁻¹ x)
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have he2 : e * e = e := ho.idem
  have hc : e * cA D e = 0 := he.2
  obtain ⟨ε, hε, halg⟩ := GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum he
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hsplit : (((1 : GA D (G.V (.top j))), conjPt S j k) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) =
      (1, resG _ ε (conjPt S j k)) * (1, resG _ (1 - ε) (conjPt S j k)) := by
    rw [Prod.mk_mul_mk, one_mul, resG_compl _ hε]
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hS := S.N.selfDual (X := .top j) (by show j ≤ D.R.m; omega)
  have hT := S.N.selfDual (X := .top (j + 1)) (by show j + 1 ≤ D.R.m; omega)
  have hlaw := GlobalTheory.SplitLinear.law_orth hW hS hT ho hc hv.2.theta hv.2.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one e _) (suppAt_resG _ hε (conjPt S j k) halg.symm) (isDetAt_detAt he2 _ 1)
    (isDetAt_detAt he2 _ (resG _ ε (conjPt S j k)))
  have hvac : Tm (halfInd e (stdLatO S (.top t j))) = S.Z.vac (.top t j) := by
    have := hTm.vac; rwa [one_smul] at this
  rw [hsplit, map_mul, Module.End.mul_apply, GlobalTheory.T.truncatedConjugate_fixes_standardVacuum_topPair S hL ht j hj k hk e he ε hε halg]
  conv_lhs => rw [← hvac]
  refine (hlaw (halfInd e (stdLatO S (.top t j))) (isSBHalf_halfInd e _)).trans ?_
  congr 1
  · rw [detAt_one' he2, detAt_resG_eq he2 hc hε halg, GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local S ht j hj k e he]
    unfold GlobalTheory.SplitLinear.fac
    simp only [splitFacO, map_one, inv_one, one_mul]
    rw [GlobalTheory.T.topPairSourceChar_prod_localIdeles G hL j hj]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have hm : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1
        (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w))) = 1 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
      rw [GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles _ _ (valuation_gdet_kapAt S hj hk), h1, Real.one_rpow, Real.one_rpow, mul_one]
    rw [hm, Complex.ofReal_one, mul_one]
  · congr 1
    funext x
    apply halfInd_congr
    by_cases hx : IsHalf e x
    · have hinv : (conjPt S j k)⁻¹ = resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹ := by
        rw [← resG_inv_eq hε', ← _root_.mul_inv_rev, resG_compl _ hε]
      have key : actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (conjPt S j k)⁻¹ x =
          actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x :=
        calc _ = actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (1 * 1⁻¹)
              (resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹) x := by rw [one_mul, ← hinv]
          _ = actO _ _ 1 (resG _ (1 - ε) (conjPt S j k)⁻¹)
              (actO _ _ 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x) := (actO_actO _ _ _ _ _).symm
          _ = _ := actO_one_resG_compl he2 hc hε halg _ _ ((isHalf_actO _ _ _).2 hx)
      rw [key]
    · constructor <;> rintro ⟨-, h⟩ <;> exact absurd ((isHalf_actO _ _ _).1 h) hx

end GlobalTheory.TopLevelInv

end
end
end
