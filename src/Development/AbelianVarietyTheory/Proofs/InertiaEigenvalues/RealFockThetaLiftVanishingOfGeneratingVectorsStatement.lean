module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactHoweDualityIsotypicMemOfStableSubspaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMapsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishingPreservedByRealLieDerivativeStatement
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftRealPointsEquivariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenInfEquiv

theorem representation_inv_mul_left_translate {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H) (w : W) :
    ρ (γ * h)⁻¹ (ρ γ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_right_translate_inv_mul {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (u h : H) (w : W) :
    ρ u (ρ (h * u)⁻¹ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ext_apply' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext φ h = c.ρ h⁻¹ (φ ((finHom V).rangeRestrict h)) := rfl

theorem ext_left' {V : HSp D} (c : CoefA V) (J : Subgroup (Formalism.IndefR.Bridge.Gf V)) (χ : J →* ℂˣ)
    (φ : Formalism.IndefR.Bridge.Gf V → c.W)
    (hφ : φ ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ J χ) (γ : GA D V) (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext φ (γ * h) = c.ext φ h := by
  have h1 := hφ ⟨γ, hγ⟩ ((finHom V).rangeRestrict h) 1
  simp only [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h1
  have h2 : φ ((finHom V).rangeRestrict γ * (finHom V).rangeRestrict h) = c.ρ γ (φ ((finHom V).rangeRestrict h)) := h1
  rw [ext_apply', ext_apply', map_mul (finHom V).rangeRestrict, h2]
  exact representation_inv_mul_left_translate c.ρ γ h _

theorem ext_inf' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (u : GA D V) (hu : u ∈ GinfC V)
    (h : GA D V) : c.ρ u (c.ext φ (h * u)) = c.ext φ h := by
  have e1 : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    have h1 : finHom V u = 1 := hu
    show finHom V (h * u) = finHom V h
    rw [map_mul, h1, mul_one]
  rw [ext_apply', ext_apply', e1]
  exact representation_right_translate_inv_mul c.ρ u h _

theorem om_left' {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (H : IsWeilDatumO ψ S T' χS χT om) (γ : GA D S)
    (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T') (f : WO S T' → ℂ) (hf : IsThetaFunO ψ S T' f) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have e : ((γ * h, g) : GA D S × GA D T') = (γ, (1 : GA D T')) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact H.om_aut _ hγ _ (Subgroup.one_mem _) _ (H.om_pres _ _ hf)

theorem om_right' {S T' : HSp D} (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (u h : GA D S)
    (g : GA D T') (f : WO S T' → ℂ) : thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have e : ((h * u, g) : GA D S × GA D T') = (h, g) * (u, (1 : GA D T')) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem mem_of_hmodIs {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : M.Is V ip) (x : M.H) : M.e x ∈ V := h.2.1 ▸ ⟨x, rfl⟩

end GlobalTheory.DownLift.GenInfEquiv


open GlobalTheory.DownLift.GenInfEquiv in
theorem GlobalTheory.DownLift.downInt_realEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y u hu f hf l g
  have hM : R.IsModels := hG.core.models
  have hν := hM.νV i t
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Vc D i)
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Vc D i)
  haveI : (R.νV i t).IsHaarMeasure := hν.1.1
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (Vc D i) _ hν.1.1
  have hx := mem_of_hmodIs _ _ _ (hM.HV i t) y
  have hW := (hP i t).datum
  let Ψ : GA D (Vc D i) → ℂ := fun h =>
    thetaKO (R.ωP i t) h g f * (l ∘ₗ (R.cV i).ρ u) ((R.cV i).ext ((R.HV i t).e y) h)
  have hL : ∀ γ ∈ GQ (Vc D i), ∀ h, Ψ (γ * h) = Ψ h := by
    intro γ hγ h
    exact congrArg₂ (fun a b => a * (l ∘ₗ (R.cV i).ρ u) b) (om_left' hW γ hγ h g f hf)
      (ext_left' (R.cV i) _ _ _ hx γ hγ h)
  have hR : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (u, 1) f) * l (R.extV i t y h) = Ψ (h * u) := by
    intro h
    exact congrArg₂ (fun a b => a * l b) (om_right' (R.ωP i t) u h g f).symm
      (ext_inf' (R.cV i) ((R.HV i t).e y) u hu h).symm
  have key := (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D i)) (R.νV i t) _ hν.2 Ψ hL u).2
  have e1 : downInt R i t y (R.ωP i t (u, 1) f) l g = ∫ h in R.fdV i t, Ψ (h * u) ∂(R.νV i t) := by
    unfold downInt
    exact integral_congr_ae (Filter.Eventually.of_forall hR)
  have e2 : downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g = ∫ h in R.fdV i t, Ψ h ∂(R.νV i t) := rfl
  rw [e1, e2, key]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftRealPointsEquivariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.downwardThetaLift_real_points_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  first | exact @GlobalTheory.DownLift.downInt_realEquiv | exact GlobalTheory.DownLift.downInt_realEquiv | (intros; apply GlobalTheory.DownLift.downInt_realEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantBilinearFormsVanishOfIoGenerationReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GenByIo

theorem forms_vanish_of_io : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t ι B heq hlie hio P j
  let U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) := ⨅ j, LinearMap.ker (B j)
  have hU : ∀ P, P ∈ U ↔ ∀ j, B j P = 0 := fun P => by simp [U, Submodule.mem_iInf]
  have hstab : ∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U := by
    intro u hu P hP P' h
    rw [hU] at hP ⊢
    intro j
    ext l
    rw [heq j u hu P P' h l, hP j]
    rfl
  have hlie' : ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U := by
    intro τ Y hY P P' hd hP
    rw [hU] at hP ⊢
    exact hlie τ Y hY P P' hd hP
  have hio' : ∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U := fun x w => (hU _).2 (hio x w)
  obtain ⟨Q, hQ, E, -, -, hNo, hPQ⟩ := GlobalTheory.T.polynomial_mem_span_lifted_maps D G Pl0 T A Ks R F hG hF i t P
  have hQU : Q ∈ U := by
    refine Submodule.span_le.2 ?_ hQ
    rintro _ ⟨φ, w, hφ, rfl⟩
    exact GlobalTheory.T.compactHoweDuality_isotypic_mem_of_stable_subspace D G Pl0 T A Ks R F hG hF i t U hstab hlie' hio' φ hφ w
  have hN : B j (P - Q) = 0 :=
    hNo (B j) (fun u hu P₁ _ P₂ h l => heq j u hu P₁ P₂ h l) _ hPQ
  have := (hU Q).1 hQU j
  rw [map_sub, this, sub_zero] at hN
  exact hN

end GlobalTheory.GenByIo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantBilinearFormsVanishOfIoGenerationRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  exact @GlobalTheory.GenByIo.forms_vanish_of_io
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealFockThetaLiftVanishingOfGeneratingVectors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GenRealFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P Q : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (P + Q) = R.ptP i t P + R.ptP i t Q := by
  unfold RealDat.ptP; exact map_add _ _ _

theorem pureTensor_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (c • P) = c • R.ptP i t P := by
  unfold RealDat.ptP; exact map_smul _ _ _

theorem downInt_add_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [thetaKO, add_mul]

theorem downInt_smul_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO, mul_assoc]

theorem downInt_add_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l l' : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l' (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y f (l + l') g = downInt R i t y f l g + downInt R i t y f l' g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [mul_add]

theorem downInt_smul_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y f (c • l) g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_bilin (R : RealDat D A Ks) (F : Face D A) (hG : GlobalTheory.LiftRows.Given R F) (hP : R.FullP)
    (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∃ B : GA D (Wc D i) → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ,
      ∀ g P l, B g P l = downInt R i t y (R.ptP i t P) l g := by
  have hth := hG.core.thP.pt_theta i t
  have hint := fun f l g hf => GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y f l g hf
  refine ⟨fun g => LinearMap.mk₂ ℂ (fun P l => downInt R i t y (R.ptP i t P) l g) ?_ ?_ ?_ ?_, fun g P l => rfl⟩
  · intro P Q l
    rw [pureTensor_add, downInt_add_f _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l g (hth Q))]
  · intro c P l
    rw [pureTensor_smul, downInt_smul_f, smul_eq_mul]
  · intro P l l'
    exact downInt_add_l _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l' g (hth P))
  · intro c P l
    rw [downInt_smul_l, smul_eq_mul]

theorem gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hio P l g
  obtain ⟨B, hB⟩ := exists_bilin R F hG hP i t y
  have hth := hG.core.thP.pt_theta i t
  have key := (GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real) D G Pl0 T A Ks R F hG hP i t (GA D (Wc D i)) B ?_ ?_ ?_ P g
  · rw [← hB, key, LinearMap.zero_apply]
  · intro j u hu P P' e l
    rw [hB, hB, e]
    exact (GlobalTheory.T.downwardThetaLift_real_points_equivariant) D G Pl0 T A Ks R F hG hP i t y u hu _ (hth P) l j
  · intro τ Y hY P P' hd h0 j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    refine (GlobalTheory.T.thetaLift_vanishing_preserved_by_realLieDerivative) D G Pl0 T A Ks R F hG hP i t y τ Y hY P P' hd l (fun g' => ?_) j
    rw [← hB, h0 g', LinearMap.zero_apply]
  · intro x w j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    exact hio x w l j

end GlobalTheory.GenRealFock
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealFockThetaLiftVanishingOfGeneratingVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.realFockThetaLift_vanishing_of_generating_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  first | exact @GlobalTheory.GenRealFock.gen | exact GlobalTheory.GenRealFock.gen | (intros; apply GlobalTheory.GenRealFock.gen <;> assumption)
end
end
