module

public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 → ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  first | exact @GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | exact GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | (intros; apply GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LieSum

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Mem.LiftGen Filter
open scoped Topology Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hasDerivAt_apply {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) {f : ℝ → WO S T → ℂ}
    (e : ∀ t, ((u t).1 : WO S T → ℂ) = f t) (w : WO S T) :
    HasDerivAt (fun t => f t w) ((A.1 : WO S T → ℂ) w) 0 := by
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (e t) w).symm)

theorem theta_nOp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (hψ : IsStdChar D ψ (-1)) (X : Matrix (Ix S T) (Ix S T) ℂ) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (l : ℂ) : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + l • F).1 := by
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, -, hn⟩ := GlobalTheory.Mem.Lift.ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  have hxd : ∀ (X : Matrix (Ix S T) (Ix S T) ℂ) (f : thetaSub ψ S T) (F : BB ψ S T),
      (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (rhoV hψ σ S T) (HM S T) X F).1 := by
    intro X f F hF
    have e : F = J f := QB_ext fun w => by rw [hF, hc]
    rw [e, ← hn, hc]
  have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
  rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
  exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem l hF)

theorem isLittleO_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) :
    (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t := by
  have h : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  rw [hasDerivAt_iff_isLittleO] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => sub_zero t)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]

theorem hasDerivAt_of_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (h : (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => Φ (u t)) (Φ A) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => (sub_zero t).symm)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]



theorem image_deriv_add {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (z₁ : u₃ 0 = u₁ 0) (zv : v 0 = A₂)
    (hnorm : ∀ t : ℝ, ‖Φ (u₃ t - u₁ t - (t : ℂ) • v t)‖ = ‖Φ (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖) :
    Φ A₃ = Φ (A₁ + A₂) := by
  have hid : ∀ t : ℝ, u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂) = (u₃ t - u₁ t - (t : ℂ) • v t) +
      (t : ℂ) • (v t - v 0) + (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
    rw [z₁, zv]
    simp only [smul_sub, smul_add]
    abel
  have hD : HasDerivAt (fun t => Φ (u₃ t)) (Φ (A₁ + A₂)) 0 := by
    apply hasDerivAt_of_rem
    have o1 := isLittleO_rem Φ d₁
    have o2' := (isLittleO_rem Φ d₂).norm_left
    have o2 : (fun t : ℝ => Φ (u₃ t - u₁ t - (t : ℂ) • v t)) =o[𝓝 0] fun t => t := by
      rw [← Asymptotics.isLittleO_norm_left]
      exact o2'.congr_left fun t => (hnorm t).symm
    have hg : Tendsto (fun t => Φ (v t - v 0)) (𝓝 0) (𝓝 0) := by
      have := ((Φ.continuous.tendsto _).comp dv.continuousAt).sub_const (Φ (v 0))
      rw [sub_self] at this
      refine this.congr fun t => ?_
      simp only [Function.comp, map_sub]
    have o3 : (fun t : ℝ => Φ ((t : ℂ) • (v t - v 0))) =o[𝓝 0] fun t => t := by
      have := (Asymptotics.isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).2 hg)
      refine this.congr (fun t => ?_) (fun t => ?_)
      · beta_reduce
        rw [map_smul, Complex.coe_smul]
      · simp
    have hΦ : ∀ t : ℝ, Φ (u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂)) = Φ (u₃ t - u₁ t - (t : ℂ) • v t) +
        Φ ((t : ℂ) • (v t - v 0)) + Φ (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
      rw [hid t, map_add (f := _), map_add (f := _)]
    exact ((o2.add o3).add o1).congr_left fun t => (hΦ t).symm
  have h3 : HasDerivAt (fun t => Φ (u₃ t)) (Φ A₃) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) d₃
  exact h3.unique hD



theorem sum_of_curves (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (γ₁ γ₂ : ℝ → GA D S × GA D T) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1)
    (F : WO S T → ℂ) (hF : IsThetaFunO ψ S T F) {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (e₁ : ∀ t, ((u₁ t).1 : WO S T → ℂ) = om (γ₁ t) F)
    (e₂ : ∀ t, ((u₂ t).1 : WO S T → ℂ) = om (γ₂ t) F)
    (e₃ : ∀ t, ((u₃ t).1 : WO S T → ℂ) = om (γ₁ t * γ₂ t) F)
    (ev : ∀ t, ((v t).1 : WO S T → ℂ) = om (γ₁ t) A₂.1)
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (hA₂ : IsThetaFunO ψ S T A₂.1) : (A₃.1 : WO S T → ℂ) = A₁.1 + A₂.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hk : ∀ (p : GA D S × GA D T) (a b : BB ψ S T), IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro p a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have z₁ : u₃ 0 = u₁ 0 := QB_ext fun x => congrFun
    (by rw [e₃, e₁, h₁, h₂, one_mul] : ((u₃ 0).1 : WO S T → ℂ) = (u₁ 0).1) x
  have z₂ : ((u₂ 0).1 : WO S T → ℂ) = F := by rw [e₂, h₂, map_one, Module.End.one_apply]
  have zv : v 0 = A₂ := QB_ext fun x => congrFun
    (by rw [ev, h₁, map_one, Module.End.one_apply] : ((v 0).1 : WO S T → ℂ) = A₂.1) x
  have th₂ : ∀ t, IsThetaFunO ψ S T (u₂ t).1 := fun t => by rw [e₂]; exact hW.om_pres _ _ hF
  have hnorm : ∀ t : ℝ, ‖toL2 _ _ (μ.restrict 𝓕) (u₃ t - u₁ t - (t : ℂ) • v t)‖ =
      ‖toL2 _ _ (μ.restrict 𝓕) (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖ := fun t => by
    have ea : ((u₃ t - u₁ t - (t : ℂ) • v t).1 : WO S T → ℂ) =
        ((u₃ t).1 : WO S T → ℂ) - (u₁ t).1 - (t : ℂ) • ((v t).1 : WO S T → ℂ) := rfl
    have eb : ((u₂ t - u₂ 0 - (t : ℂ) • A₂).1 : WO S T → ℂ) =
        ((u₂ t).1 : WO S T → ℂ) - (u₂ 0).1 - (t : ℂ) • (A₂.1 : WO S T → ℂ) := rfl
    refine hk (γ₁ t) _ _ ?_ ?_
    · rw [eb]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (th₂ t) (th₂ 0)) ((thetaSub ψ S T).smul_mem _ hA₂)
    · rw [ea, eb, z₂, e₃, e₁, ev, e₂, map_mul, Module.End.mul_apply, map_sub, map_sub, map_smul]
  have key : toL2 _ _ (μ.restrict 𝓕) A₃ = toL2 _ _ (μ.restrict 𝓕) (A₁ + A₂) :=
    image_deriv_add _ d₁ d₂ d₃ dv z₁ zv hnorm
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (A₃ - (A₁ + A₂))
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((A₃ - (A₁ + A₂)).1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (A₃ - (A₁ + A₂)).1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  exact sub_eq_zero.1 h5

end GlobalTheory.Mem.LieSum



open Classical in
theorem GlobalTheory.Mem.LieSum.hasDerivAt_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  intro D V W θ ψ χS χT ω τ hθ hω X hX Y hY F F₁ F₂ hF h₁ h₂ z
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hc := hω.om_cont
  let γ₁ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, 1)
  let γ₂ : ℝ → GA D V × GA D W := fun t => (1, oneP θ W τ Y t)
  let γ₃ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, oneP θ W τ Y t)
  have hγ : ∀ t, γ₃ t = γ₁ t * γ₂ t := fun t => by
    simp only [γ₁, γ₂, γ₃, Prod.mk_mul_mk, mul_one, one_mul]
  have m₁ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₁ t) k l)
      (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k l) 0 := fun k l => by
    simp only [γ₁, GlobalTheory.RealWeil.mM_apply, GlobalTheory.Mem.Lift.WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one,
      GlobalTheory.WeilVacMove.compAt_one, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ (GlobalTheory.Mem.Lift.WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  have m₂ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₂ t) k l)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) k l) 0 := fun k l => by
    simp only [γ₂, GlobalTheory.RealWeil.mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _
  have m₃ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₃ t) k l)
      (∑ j, (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k j * GlobalTheory.RealWeil.mM θ V W (γ₂ 0) j l +
        GlobalTheory.RealWeil.mM θ V W (γ₁ 0) k j * GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) j l)) 0 :=
    fun k l => by
      simp only [hγ, map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (m₁ k j).mul (m₂ j l)
  obtain ⟨l₁, g₁⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₁
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, one_mem _⟩) _ m₁
  obtain ⟨l₂, g₂⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₂
    (continuous_const.prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₂
  obtain ⟨l₃, g₃⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₃
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₃]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₃
  have eF := GlobalTheory.RealWeil.coe_toB hψ F hF
  have hFb : IsThetaFunO ψ V W (GlobalTheory.RealWeil.toB hψ F hF).1 := by rw [eF]; exact hF
  obtain ⟨u₁, e₁, d₁⟩ := g₁ _ hFb
  obtain ⟨u₂, e₂, d₂⟩ := g₂ _ hFb
  obtain ⟨u₃, e₃, d₃⟩ := g₃ _ hFb
  have hA₂ := GlobalTheory.Mem.LieSum.theta_nOp h hψ (GlobalTheory.RealWeil.blk (Pi.single τ Y) fun _ => 1) _ hFb l₂
  obtain ⟨v, ev, dv⟩ := g₁ _ hA₂
  rw [eF] at e₁ e₂ e₃
  have k₁ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₁ e₁ z
  have k₂ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₂ e₂ z
  have k₃ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₃ e₃ z
  have hs := GlobalTheory.Mem.LieSum.sum_of_curves hψ hW γ₁ γ₂
    (by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl)
    (by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl) F hF e₁ e₂ (fun t => by rw [e₃, hγ]) ev d₁ d₂ d₃ dv hA₂
  rw [hs, Pi.add_apply, k₁.unique (h₁ z), k₂.unique (h₂ z)] at k₃
  exact k₃
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_realPlaceDerivatives_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  first | exact @GlobalTheory.Mem.LieSum.hasDerivAt_add | exact GlobalTheory.Mem.LieSum.hasDerivAt_add | (intros; apply GlobalTheory.Mem.LieSum.hasDerivAt_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

def frOf {D : D7} (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ)
    (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : Fr V where
  ε τ := sgB (p τ)
  fr τ := (B τ)⁻¹
  fr_unit τ := (isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (onb_facts (h τ)).1)
  fr_gram τ := by
    obtain ⟨u, g, -⟩ := onb_facts (h τ)
    rw [← g]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ u, conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ u, Matrix.one_mul, Matrix.mul_one]

variable {D : D7} {V : HSp D} {s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {p : D.what₂.Tau → ℕ}

theorem frOf_onb (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).onb = B := by
  funext τ
  exact nonsing_inv_nonsing_inv _ (onb_facts (h τ)).1

theorem frOf_cart (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).cart = s := by
  funext τ
  obtain ⟨u, -, c⟩ := onb_facts (h τ)
  change ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (sgB (p τ)) * (B τ)⁻¹ = s τ
  rw [nonsing_inv_nonsing_inv _ u, ← c, mul_nonsing_inv_cancel_right _ _ u]

theorem pure_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (P : MvPolynomial ι ℂ) :
    pureTensorL A (0 : X → ℂ) P = 0 := by
  have h : ∀ l : List ι, l.foldr (fun i g => A i g) (0 : X → ℂ) = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih, hA]
  have hz : pureTensorL A (0 : X → ℂ) = 0 := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.zero_apply]
    exact h _
  rw [hz, LinearMap.zero_apply]

end GlobalTheory.WeilReal

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

theorem comb {R : Type} [AddCommGroup R] [Module ℂ R] (a b q P : R) (h c d : ℂ) (hq : a + b = q + h • P) :
    q + (h + c - d) • P = (a + (-d) • P) + (b + c • P) := by
  have e : q = a + b - h • P := eq_sub_of_add_eq hq.symm
  rw [e]
  module

theorem realAllO : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  intro D ψ S T χS χT om hd _ θ sS sT BS BT pS pT hp τ αS αT hαS hαT XS XT hXS hXT f hf hv P x
  obtain ⟨A, hA⟩ : ∃ A : Fr S, A = frOf S sS BS pS hp.onbS := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fr T, B = frOf T sT BT pT hp.onbT := ⟨_, rfl⟩
  have cA : A.cart = sS := hA ▸ frOf_cart hp.onbS
  have cB : B.cart = sT := hB ▸ frOf_cart hp.onbT
  have oA : A.onb = BS := hA ▸ frOf_onb hp.onbS
  have oB : B.onb = BT := hB ▸ frOf_onb hp.onbT
  have eA : A.ε τ = sgB (pS τ) := by rw [hA]; rfl
  have eB : B.ε τ = sgB (pT τ) := by rw [hB]; rfl
  have rA : A.fr τ = (BS τ)⁻¹ := by rw [hA]; rfl
  have rB : B.fr τ = (BT τ)⁻¹ := by rw [hB]; rfl
  have pt : pureTensorO ψ θ S T sS sT BS BT f = ptF ψ θ A B f := by
    rw [ptF, cA, cB, oA, oB]
  rw [pt]
  have lin : ∀ (g : WO S T → ℂ) (Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (Q + Q') = ptF ψ θ A B g Q + ptF ψ θ A B g Q' := fun g Q Q' =>
    map_add (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) Q Q'
  have lsm : ∀ (g : WO S T → ℂ) (c : ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (c • Q) = c • ptF ψ θ A B g Q := fun g c Q =>
    map_smul (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) c Q
  by_cases f0 : f = 0
  · subst f0
    have z0 : ∀ Q, ptF ψ θ A B 0 Q = 0 := fun Q => by
      refine pure_zero _ (fun k => ?_) Q
      funext y
      simp [aPlusAll, aPlus, crea, Datum.dRho, heisO]
    simp only [z0, map_zero]
    exact hasDerivAt_const _ _
  obtain ⟨f₀, hv0, hne⟩ := GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction D S T A B θ ψ hp.std hp.inf f hf f0
  obtain ⟨κS, κT, hκ⟩ := GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars D S T A B θ ψ χS χT om τ hp.inf hd
  have k0 := hκ f₀ hv0.1 (hv0.2 τ)
  have all := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT om f₀ τ αS αT hp.inf hd hαS hαT hv0
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have hz' : f₀ z ≠ 0 := hz
  have one : ∀ c : ℂ, ptF ψ θ A B f₀ (c • (1 : MvPolynomial _ ℂ)) z = c * f₀ z := fun c => by
    rw [lsm]
    have e1 : ptF ψ θ A B f₀ 1 = f₀ := GlobalTheory.FockIndep.pure_one f₀
    rw [e1]
    rfl
  have eS : κS XS = -((αT : ℂ) * XS.trace) := by
    have e := (k0.1 XS hXS 1 z).unique (all.1 XS hXS 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have eT : κT XT = (αS : ℂ) * XT.trace := by
    have e := (k0.2 XT hXT 1 z).unique (all.2 XT hXT 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have kf := hκ f hf (by rw [cA, cB]; exact hv)
  have ht : IsThetaFunO ψ S T (ptF ψ θ A B f P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hp.std hp.inf _ _ _ _ hf P
  have sm := GlobalTheory.T.weilDatum_realPlaceDerivatives_add D S T θ ψ χS χT om τ hp.inf hd XS hXS XT hXT _ _ _ ht (kf.1 XS hXS P) (kf.2 XT hXT P) x
  have uS := (onb_facts (hp.onbS τ)).1
  have uT := (onb_facts (hp.onbT τ)).1
  have frA : (A.fr τ * XS * (A.fr τ)⁻¹) = (BS τ)⁻¹ * XS * BS τ := by
    rw [rA, nonsing_inv_nonsing_inv _ uS]
  have frB : (B.fr τ * XT * (B.fr τ)⁻¹) = (BT τ)⁻¹ * XT * BT τ := by
    rw [rB, nonsing_inv_nonsing_inv _ uT]
  have q := fock_eq_quad τ (pS τ) (pT τ) (hp.onbS τ) (hp.onbT τ) hXS hXT P
  have e : ptF ψ θ A B f (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
      (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace - (αT : ℂ) * XS.trace) • P) x =
      ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * XS * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS XS • P) x +
      ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * XT * (B.fr τ)⁻¹) P + κT XT • P) x := by
    rw [← Pi.add_apply (ptF ψ θ A B f _), ← lin, frA, frB, eS, eT, eA, eB, comb _ _ _ _ _ _ _ q]
  rw [e]
  exact sm

end GlobalTheory.WeilReal

end
end
end
