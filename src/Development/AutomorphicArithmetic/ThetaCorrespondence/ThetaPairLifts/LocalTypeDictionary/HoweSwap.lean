module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPai
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerV
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalHoweTensorProductTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationRankLeDim
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaKernelCondition

section

@[expose] public section

section
open NumberField IsDedekindDomain

abbrev _root_.GlobalTheory.T.TwistedThetaKernelCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaJetCondition

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

abbrev _root_.GlobalTheory.T.TwistedThetaJetCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes


theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  first | exact @GlobalTheory.HoweRealSmall.howe_real_ker' | exact GlobalTheory.HoweRealSmall.howe_real_ker' | (intros; apply GlobalTheory.HoweRealSmall.howe_real_ker' <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalHoweTransferRealPlace

section

@[expose] public section

section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.HoweGlobal.RealTransfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealActs
theorem howe_real_place_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have PA : PolActs Bs G.M om := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair
  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  have key : ∀ N : Submodule ℂ ↥P, relInf Bs G om ≤ N → (∀ g ∈ opInf Bs G om, ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.1 γ hγ
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.2.1 k hk
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.1 γ hγ
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inr ⟨γ, hγ, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.2 k hk
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inl ⟨k, hk, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨_root_.GlobalTheory.T.polarization_rank_le_dim hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    refine ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot.lie γ hγ f hf _ hA
    · show R.p (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hg x hx
    have hx' : R.p (x : SInf F _) = 0 := hx
    show R.p ((g x : ↥P) : SInf F _) = 0
    rcases hg with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have := hM.real.cpt k hk x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.acts_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
    · have := hM.real.lie γ hγ x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
end GlobalTheory.HoweGlobal.RealTransfer
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.global_howe_transfer_real_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | exact _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweSwap

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory.HoweGlobalPair
theorem stageV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M Bs.ψ Bs.emb hM.triple.geo.hM.std T
  have hloc := _root_.GlobalTheory.T.global_howe_transfer_real_place hP F E σ Bs a a' G Xc om om' R Rf hM hreal
  have hfl := fun v => locV hM v
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.global_howe_tensor_product_transfer hP F E σ Bs a a' G Xc om om' R Rf hM N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))
    (GlobalTheory.HoweGlobal.opInf Bs G om) (fun v => GlobalTheory.HoweGlobal.opFin G om v.1)
    (GlobalTheory.HoweGlobal.relInf Bs G om) (fun v => GlobalTheory.HoweGlobal.relFin G om v.1)
    (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerV hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerV hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobal.decomp t
    refine ⟨T, hT, m, 0, fun j => ((f j : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F (Fin a × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) else G.M.vac v,
      Fin.elim0, Fin.elim0, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hM.triple.geo.hM.vac v).1

    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · simp

    · rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp
theorem allV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne ΦD hΦ
  by_contra hc
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb (hN.1.1 hΦ) Xc.T
  apply hne
  refine le_antisymm hN.1.1 fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb hΨ T
  rcases _root_.UpperTheory.Lit.HoweDuality.stageV_alt hP F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h ΦD hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M Bs.ψ Bs.emb hT' hΦT)) hc
theorem twisted_theta_kernel_condition : _root_.GlobalTheory.T.TwistedThetaKernelCondition := fun hR hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne =>
  _root_.UpperTheory.Lit.HoweDuality.allV_alt hP F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
theorem twisted_theta_jet_condition : _root_.GlobalTheory.T.TwistedThetaJetCondition := fun hR _ F E _ _ _ _ _ σ a a' Bs G Xc om om' R Rf hM N hN hne =>
  allVp F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
end UpperTheory.Lit.HoweDuality
end
end
end
end
