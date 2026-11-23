module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalizationAtMember
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMemStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.CuspOfParam

theorem goodRow_cuspidal : ∀ (D : D7) (Rw : RowSide D), Nonempty D.nd.Loc → (∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ := by
  intro D Rw hLoc hW hG j hj1 hj2 σ hσ hgood
  obtain ⟨i⟩ := hLoc
  obtain ⟨π, hcsd, hralg, hsplit, -, -, -⟩ := hG j hj1 hj2 σ hσ hgood
  have hr : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hiso : ∀ w, Formalism.MainNotions.N.isoLoc D.nd D.naut [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] w = D.naut.locG π w := by
    intro w
    simp [Formalism.MainNotions.N.isoLoc, Formalism.MainNotions.N.spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have hpar : Formalism.MainNotions.N.HasParamW D.nd D.naut i σ [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hr, le_refl 1⟩
    · simp [Formalism.MainNotions.N.rankIso]
    · intro w hw
      rw [hiso w, hsplit w hw, hW i σ w]
  have h := D.bc_tie i σ _ hpar
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hcsd)
    (by
      intro p hp τ
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨hnd, hz⟩ := (D.naut.ralg_def π).1 hralg τ
      refine ⟨hnd, fun z hz' => ?_⟩
      obtain ⟨n, hn⟩ := hz z hz'
      exact ⟨n, by rw [hn]; simp⟩)
  show D.ntypes.bc σ = {(D.R.r, 1)}
  rw [h]
  simp

end GlobalTheory.HeightCounting.CuspOfParam
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocWOfNTrue

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt

theorem locW_of_nTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    ∀ i σ w, D'.naut.locW i σ w = Rw.locR σ w := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  intro i σ w
  rw [e1]
  exact Au.locW i σ w
end GlobalTheory.GalLoc.RowParamAt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalGaloisParameterAtPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
theorem localGalois_parameter_mem_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  intro hN _ hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hN hL) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hN hL))
    (_root_.GlobalTheory.T.exists_twisted_place_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c _ H Rw hRw
  obtain ⟨⟨hp, hl⟩, v, hv⟩ := H
  have hW := _root_.GlobalTheory.GalLoc.RowParamAt.locW_of_nTrue_alt c.a.nt Rw hRw
  refine GlobalTheory.TwInputs.rowParam_of_cuspParam (w.D Z) Rw (hp Rw hRw) ?_ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw _)
  intro j h1 h2 σ hσ hg
  obtain ⟨i, -, -⟩ := hl v hv j h1 h2 σ hσ
  exact GlobalTheory.HeightCounting.CuspOfParam.goodRow_cuspidal (w.D Z) Rw ⟨i⟩ hW (hp Rw hRw) j h1 h2 σ hσ hg
end GlobalTheory.GalLoc.RowParamAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.local_param_at_member_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | exact _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt <;> assumption)
end
end
end
end
