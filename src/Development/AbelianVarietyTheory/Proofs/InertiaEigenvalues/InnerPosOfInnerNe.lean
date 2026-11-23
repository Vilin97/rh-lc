module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointInjectiveSurjectiveAndPositiveScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSumOfRank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfInnerEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpOfTranslates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFinIdem

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PartsSpanProof

theorem exists_isFinIdem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v, IsFinIdem D v f := by
  rcases h with ⟨⟨⟨-, -, v, ε, hv, he⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hv, rfl⟩, -⟩
  · exact ⟨v, ε, hv, he⟩
  · exact ⟨v, ε, hv, rfl⟩

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]



theorem partsSpan : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i S, PartsSpan R i S := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF i S
  have hLP := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF i
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i
  obtain ⟨inj, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  let ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Wc D i)) //
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S
      x.1 x.2.1 x.2.2}
  have keep : ∀ x : ι, ∀ U ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) x.1.2.2 U ∈ R.Wall i (sg0 D A) := by
    rintro ⟨⟨P, d, B⟩, e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hB, hc⟩ U hU
    obtain ⟨v, hv⟩ := exists_isFinIdem hP
    exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall hLP v f hv α hα B hB hc U hU
  have hex : ∀ x : ι, ∃ h : Module.End ℂ (R.HW i (sg0 D A)).H, ∀ y,
      (R.HW i (sg0 D A)).e (h y) = heckeOn (R.MW i (sg0 D A)) x.1.2.2 ((R.HW i (sg0 D A)).e y) :=
    fun x => exists_lift _ inj _ fun y => hr ▸ keep x _ (hmem y)
  choose op hop using hex
  have hcomm : Formalism.L2.Col.PairComm op := fun x x' => by
    refine LinearMap.ext fun y => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hop, hop, hop, hop]
    exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (J := levW R i)
      (GlobalTheory.HeckeAdjoint.realUnif D _) x.2 x'.2 (hlv y v)
  have hadj : ∀ x : ι, ∃ x', op x' = LinearMap.adjoint (op x) := by
    intro x
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D x.1.1) x.2
    let x' : ι := ⟨(x.1.1, dualLab x.1.2.1, B'), hB'⟩
    refine ⟨x', ?_⟩
    rw [LinearMap.eq_adjoint_iff]
    intro a b
    rw [hip, hip, hop, hop]
    unfold ipAt
    congr 1
    exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D (Wc D i) _ R.θ (R.MW i (sg0 D A)) (levW R i) _ S (R.νW i) (R.fdW i)
      hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 hS x.1.1 (dualLab x.1.2.1) B' x.1.2.2 hB'
      (by rw [dualLab_dualLab]; exact x.2) _ (hmem a) _ (hmem b) (keep x' _ (hmem a)) (keep x _ (hmem b))
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition op hcomm hadj
  classical
  unfold PartsSpan
  refine eq_top_iff.2 (h2 ▸ iSup_le fun y => ?_)
  refine le_iSup_of_le (fun P d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B then y ⟨(P, d, h.choose), h.choose_spec⟩ else 0) ?_
  intro x hx
  rw [h1, Submodule.mem_iInf] at hx
  show (R.HW i (sg0 D A)).e x ∈ partFull _ _ _ _ _ _
  unfold partFull
  refine Submodule.mem_inf.2 ⟨hmem x, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hE : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B := ⟨B, hB⟩
  rw [dite_eq_left hE]
  have e1 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d, hE.choose), hE.choose_spec⟩)
  have e2 := congrArg (R.HW i (sg0 D A)).e e1
  rw [hop, map_smul] at e2
  rw [← e2]
  exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.labelUnique (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D)
    P d B _ hB hE.choose_spec _ (hlv x v)

end GlobalTheory.PartsSpanProof

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalarStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.fockVacuum_pairing_polynomial_translates_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ u ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  first | exact @GlobalTheory.VacPairSchur.pair_eq | exact GlobalTheory.VacPairSchur.pair_eq | (intros; apply GlobalTheory.VacPairSchur.pair_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacOmFin

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.FactorInf

theorem fockVac_om_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D}
    (hθ : IsInfFam θ) {γ : GA D T} (hγ : γ ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (1, γ) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (mt T γ) * z * compAt θ τ (mt S (1 : GA D S)⁻¹) = z := fun z => by
    rw [inv_one, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hγ τ,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (Subgroup.one_mem _) τ, Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (1, γ)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem factInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FactInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ u hu γ hγ P P'
  have hW := hL.thP.ωP i t
  have hθ : IsInfFam R.θ := hL.models.inf
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP at this
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at this
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  set f₁ := R.ωP i t (1, γ) (R.vP i t) with hf₁
  have hth1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₁ := hW.om_pres _ _ hth
  have hvac1 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₁ :=
    fun τ => fockVac_om_fin hW hθ hγ τ _ hth (hvac τ)
  have hmul : R.ωP i t (1, u * γ) (R.ptP i t P) = R.ωP i t (1, u) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f₁ P) := by
    have e : ((1 : GA D (Vc D i)), u * γ) = (1, u) * (1, γ) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    unfold RealDat.ptP
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW R.θ hθ 1 (Subgroup.one_mem _) γ hγ _ _ _ _ _ P hth
  obtain ⟨c, hc⟩ := GlobalTheory.T.fockVacuum_pairing_polynomial_translates_scalar D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank)
    (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ))
    (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) μ 𝓕 hμ u hu P P'
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  rw [hmul]
  unfold RealDat.ptP
  rw [hc f₁ _ hth1 hth hvac1 hvac, hc _ _ hth hth hvac hvac]
  unfold coef
  rw [← hf₁]
  field_simp

end GlobalTheory.RawLift.FactorInf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatSpanOfLaws

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RatSpanProof

theorem ratSpan_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t
  exact GlobalTheory.HeckeClassSums.span_jV hL.models.HV hL.models.jV i t

end GlobalTheory.RatSpanProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RawLiftOntoOfUpInj

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory



theorem rawLift_onto_of_upInj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R → (∀ i, UpInj R i A.μ0) → ThOnto R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hS hU i
  obtain ⟨th, hth⟩ := hL.exists_isRaw i A.μ0
  have hsurj := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).1 (hU i th hth)
  rw [hS i A.μ0, Submodule.map_top]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hL.thP.thF_mem i A.μ0 x
  · intro w hw
    rw [← (hL.models.HW i (sg0 D A)).2.1] at hw
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, (hth x).symm⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerPosOfInnerNe

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem innerPos_of_innerNe {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : InnerNe R i t S) : InnerPos R i t S := by
  unfold InnerPos
  intro th hth c
  have h' := h th hth c
  obtain ⟨l, hl, hx⟩ := h'
  have key := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).2 (part R i S c) l hl hx
  obtain ⟨l', hl', hx', -⟩ := key
  exact ⟨l', hl', hx'⟩

theorem rawLift_main : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D →
    ThOnto R ∧ ∀ i t, UpInj R i t ∧ InnerPos R i t ∅ ∧ PartsSpan R i ∅ := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF hR
  have lp : ∀ i, LevProd R i := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF
  have tr : ∀ i, TransLaws R i := GlobalTheory.RawLiftTrans.transLaws hC D G Pl0 T A Ks R F hL hF
  have lf : ∀ i t, LevFix R i t := GlobalTheory.RawLift.LevelFix.levFix D G Pl0 T A Ks R F hL hF
  have vn : ∀ i t, VecNe R i t := vecNe D G Pl0 T A Ks R F hL hF
  have fs : ∀ i t, FinSum R i t := fun i t =>
    GlobalTheory.RawLift.finSum_of_rallis hC D G Pl0 T A Ks R F hL hF hR i t (GlobalTheory.T.downwardLift_adjoint_eq_upwardThetaIntegral hC D G Pl0 T A Ks R F hL hF i t) (lf i t)
      (GlobalTheory.RawLift.FactorInf.factInf D G Pl0 T A Ks R F hL hF i t) (GlobalTheory.RawLift.RealLowPf.realLow D G Pl0 T A Ks R F hL hF i t) (vn i t) (lp i) (tr i)
  have fm : ∀ i t, FinMult R i t := GlobalTheory.RawLift.LocalFactor.finMult D G Pl0 T A Ks R F hL hF
  have bs : ∀ i t, BadSupp R i t := GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces D G Pl0 T A Ks R F hL hF
  have ls : ∀ i t, LocSmall R i t := fun i t =>
    GlobalTheory.RawLift.Small.locSmall D G Pl0 T A Ks R F hL hF i t (bs i t) (GlobalTheory.RawLift.GoodModulus.goodMod D G Pl0 T A Ks R F hL hF i t)
      (GlobalTheory.IndexCount.indexSum_holds D G Pl0 T A Ks R F hL hF i)
  have up : ∀ i t, UpInj R i t := fun i t =>
    GlobalTheory.UpInj.upInj_holds D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (lp i) (tr i)
  refine ⟨GlobalTheory.rawLift_onto_of_upInj D G Pl0 T A Ks R F hL hF (GlobalTheory.RatSpanProof.ratSpan_of_laws D G Pl0 T A Ks R F hL hF) (fun i => up i A.μ0),
    fun i t => ⟨up i t, ?_, GlobalTheory.PartsSpanProof.partsSpan hC D G Pl0 T A Ks R F hL hF i ∅⟩⟩
  exact innerPos_of_innerNe R i t ∅
    (GlobalTheory.RawLift.innerNe_spherical D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (bs i t) (lp i) (tr i))

end GlobalTheory.RawLift
end
end
