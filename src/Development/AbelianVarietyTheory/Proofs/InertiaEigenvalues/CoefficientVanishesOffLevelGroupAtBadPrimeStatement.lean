module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupportStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pf : Finset (Pl D.host.E)) (ea e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsIdemSum ea Pf → IsSplitIdem D e → e * ea = e → IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₁ → IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₂ → (∀ x x' : WO S T, (∀ a b, (e + cA D e) * x a b = (e + cA D e) * x' a b) → Φ₁ x ≠ 0 → Φ₂ x' ≠ 0 → False) → ∀ Ω : Module.End ℂ (WO S T → ℂ), (∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ω g)) → (∀ y : WO S T, IsHalf e y → ∀ g, IsThetaFunO ψ S T g → Ω (heisO ψ S T y g) = heisO ψ S T y (Ω g)) → thetaIP μ 𝓕 (Tm Φ₁) (Ω (Tm Φ₂)) = 0 := by
  first | exact @GlobalTheory.BadOrth.orth_of_disjoint | exact GlobalTheory.BadOrth.orth_of_disjoint | (intros; apply GlobalTheory.BadOrth.orth_of_disjoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace



theorem vec_read_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t P hP e f hPI k hk
  obtain ⟨⟨hψ, hvac⟩, ea, hIS, hth⟩ := hL.thP.vP i t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hvP : R.vP i t = Tm (datP R i t ea) := hall Tm hTm
  have lV := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βV i)
  have lW := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βW i)
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lV
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lW
  have hIS' := hIS
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := hIS'
  have hPm : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨rfl, rfl⟩ := GlobalTheory.Hk3.SplitMatch.idem_unique (hes P hPm) hPI
  have h1 : ∀ PP ∈ R.Pg ∪ R.Q t, IsSplitIdem D (es PP) := fun PP hPP => (hes PP hPP).1
  have h2 : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ QQ ∈ R.Pg ∪ R.Q t, QQ ≠ PP → es PP * es QQ = 0 := by
    intro PP hPP QQ hQQ hne
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP) (h1 QQ hQQ)).resolve_left fun h => hne ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(hes PP hPP).2 x hx, (hes QQ hQQ).2 x hx, h]
  have hee : es P * ea = es P := by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hPm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hinf : infPart D (cA D ea) = 0 := ho.infPart_eq
  have hSB : IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hSV)
      (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      (R.Pg ∪ R.Q t) (fun y => omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr (R.Q t) _ (R.xiR t) _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ (R.ΛV i) hSV
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ (R.ΛW i) hSW
  have hSB2 := GlobalTheory.SplitLinear.isSBHalf_actO inferInstance inferInstance 1 k⁻¹ hSB
  have hcc : cA D ea * cA D (cA D ea) = 0 := by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, hc]
  have ha : cA D ea * cA D ea = cA D ea := ho.idem
  have r1 : cA D ea * cA D (es P) = cA D (es P) := by rw [← map_mul, mul_comm, hee]
  have r2 : ea * cA D (es P) = 0 := by
    have e1 : cA D (es P) = cA D (es P) * cA D ea := by rw [← map_mul, hee]
    rw [e1, ← mul_assoc, mul_comm ea, mul_assoc, hc, mul_zero]
  have r3 : cA D ea * es P = 0 := by
    have := congrArg (cA D) r2
    rwa [map_mul, GlobalTheory.SplitOnto.cA_cA, map_zero] at this
  have r4 : ea * es P = es P := by rw [mul_comm, hee]
  have key : (cA D ea + cA D (cA D ea)) * (es P + cA D (es P)) = es P + cA D (es P) := by
    rw [GlobalTheory.SplitOnto.cA_cA]
    linear_combination r1 + r2 + r3 + r4
  have hsupp : SuppAt (cA D ea) (Wc D i) k := fun a b => by
    rw [← hk a b, ← mul_assoc, key]
  have hLaw := GlobalTheory.SplitLinear.law_orth (hF i t).datum hSV hSW ho hcc hvac.theta hvac.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one _ _) hsupp (GlobalTheory.VecInv.isDetAt_detAt _ ha _ 1) (GlobalTheory.VecInv.isDetAt_detAt _ ha _ k)
  have hω := hLaw _ hSB
  rw [← hvP] at hω
  simp only [inv_one] at hω
  exact ⟨ea, Tm, _, hIS, (hes P hPm).1, hee, rfl, hψ, hSV, hSW, hvac.theta, hvac.lat, hTm, hSB, hSB2, hvP, hω⟩

end GlobalTheory.BadPlace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  first | exact @GlobalTheory.BadPlace.vec_read_at | exact GlobalTheory.BadPlace.vec_read_at | (intros; apply GlobalTheory.BadPlace.vec_read_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace

noncomputable section

namespace GlobalTheory.BadPlace




theorem actO_one_inv_half {D : D7} {S T : HSp D} {e f : AE D} (hef : e * f = e) {γ : GA D T}
    (hγ : GlobalTheory.RawLift.TrivAt T f γ) {y : WO S T} (hy : IsHalf e y) : actO S T 1 γ⁻¹ y = y := by
  have h1 : f • Formalism.L2.Theta.mt T γ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext a b
    have := hγ a b
    rw [Matrix.sub_apply, mul_sub] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.1 this
  have h2 : Formalism.L2.Theta.mt T γ * Formalism.L2.Theta.mt T γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : f • Formalism.L2.Theta.mt T γ⁻¹ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    calc f • Formalism.L2.Theta.mt T γ⁻¹ = (f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) * Formalism.L2.Theta.mt T γ⁻¹ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (f • Formalism.L2.Theta.mt T γ) * Formalism.L2.Theta.mt T γ⁻¹ := by rw [h1]
      _ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by rw [Matrix.smul_mul, h2]
  have h4 : e • Formalism.L2.Theta.mt T γ⁻¹ = e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    rw [← hef, ← smul_smul, h3, smul_smul]
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = y := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hy a b
  have hone : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    simp only [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  unfold actO
  rw [hone, Matrix.mul_one]
  calc HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      = HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by rw [hy']
    _ = HMul.hMul (e • Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = HMul.hMul (e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [h4]
    _ = y := by rw [Matrix.smul_mul, Matrix.one_mul, hy']

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]



theorem coef_bad_vanish : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hC P hP e f hPI γ _ hTr k hk hlev
  obtain ⟨ea, Tm, c, hIS, hSe, hee, hf, hψ, hSV, hSW, hv0, hvl, hTm, hSB2, hSB1, hvP, hωk⟩ :=
    GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime D G Pl0 T A Ks R F hL hF i t P hP e f hPI k hk
  have hdisj := GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support D G Pl0 T A Ks R F hL hF i t ea hIS P hP e f hPI k hk hlev
  have hW := (hF i t).datum
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [RealDat.ptP, pureTensorO, pureTensorL_one] at this
  have hef : e * f = e := by
    rw [hf, mul_add, hSe.1, hSe.2.1, add_zero]
  have e1 := GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hC (1, γ⁻¹)
    (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) (hW.om_pres (1, γ * k) _ hth) hth
  rw [← e1, ← Module.End.mul_apply, ← map_mul]
  have e2 : ((1 : GA D (Vc D i)), γ⁻¹) * (1, γ * k) = (1, k) := by
    ext
    · exact mul_one 1
    · exact (inv_mul_cancel_left γ k)
  rw [e2, hωk, thetaInner_smul_left]
  have hz := GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) _ ea e (R.vacP i) Tm μ 𝓕 hψ hSV hSW hIS hSe hee hv0 hvl
    hTm hC _ _ hSB1 hSB2 (fun x x' hxx' h1 h2 => hdisj x x' (by rw [hf]; exact hxx') h1 h2) (R.ωP i t (1, γ⁻¹))
    (fun g hg => hW.om_pres _ _ hg) (fun y hy g hg => by
      rw [hW.om_heis _ _ _ _ hg, actO_one_inv_half hef hTr hy])
  rw [← hvP] at hz
  rw [hz, mul_zero]

end GlobalTheory.BadPlace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  first | exact @GlobalTheory.BadPlace.coef_bad_vanish | exact GlobalTheory.BadPlace.coef_bad_vanish | (intros; apply GlobalTheory.BadPlace.coef_bad_vanish <;> assumption)
end
end
