module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhaseStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCard
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriangularMul
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZeroStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  first | exact @GlobalTheory.LevelSeries.exists_invariant_form_idemSum | exact GlobalTheory.LevelSeries.exists_invariant_form_idemSum | (intros; apply GlobalTheory.LevelSeries.exists_invariant_form_idemSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCardStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  first | exact @GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | exact GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | (intros; apply GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationPreservesNorm

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.WeilUnitNorm

open MeasureTheory

theorem weil_norm_one_of_unit_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  intro D ψ S T χS χT om hW μ 𝓕 hC p f hf h1
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have key := hW.om_unit μ 𝓕 hC.1 hC.2.1 p f hf
  have hf' := hW.om_pres p f hf
  have m1 : AEStronglyMeasurable (fun w => ‖om p f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf'.cont.norm.pow 2).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf.cont.norm.pow 2).aestronglyMeasurable
  have e : nrm2 μ 𝓕 (om p f) = nrm2 μ 𝓕 f := by
    unfold nrm2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m1,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m2]
    congr 1
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    exact key
  rw [e, h1]

end GlobalTheory.WeilUnitNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationPreservesNormStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.weil_representation_preserves_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  first | exact @GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | exact GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | (intros; apply GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedVacuumTranslateSumFlipScalar

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScal

open MeasureTheory

theorem nrm2_const_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    nrm2 μ 𝓕 (c • f) = ‖c‖ ^ 2 * nrm2 μ 𝓕 f := by
  unfold nrm2
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, norm_smul, mul_pow]

theorem moved_vacuum_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (x : (AE D)ˣ) (lam : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → Y.card = flipIdx V W T m → om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ → lam = flipScal χW V W T m x := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z x lam Y hT hm hcop hTm hz hmt hx hY hYu hcard hom
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have hW := hP.1.weil
  have hf := hP.2.2.2.2.2.2.2.2
  obtain ⟨ℓ, hℓ0, hℓ⟩ := GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨r, hr, hrℓ⟩ := GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase D ψ V W χV χW om hW T eT m z x ℓ hT hm0 hmt hx hℓ
  have hth := hf.2.theta
  have h1 := hrℓ f₀ hth
  have hsum : ℓ (∑ y ∈ Y, heisO ψ V W y f₀) = (Y.card : ℂ) * ℓ f₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl fun y hy => hℓ y (hY y hy).1 f₀ hth, Finset.sum_const, nsmul_eq_mul]
  rw [hom, map_smul, hsum, smul_eq_mul] at h1
  have h2 : lam * Y.card = r * ((χW x : Circle) : ℂ)⁻¹ := mul_right_cancel₀ hℓ0 (by rw [← h1]; ring)
  obtain ⟨p, hp⟩ := hf.2.norm.1
  have hn := GlobalTheory.T.weil_representation_preserves_norm D ψ V W χV χW om hW p.1 p.2 hp (z⁻¹, 1) f₀ hth (hf.2.norm.2 p hp)
  rw [hom, nrm2_const_smul, GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y (fun y hy => (hY y hy).1) hYu p.1 p.2
    hp] at hn
  have hχ : ‖((χW x : Circle) : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
  have h3 : ‖lam‖ * Y.card = r := by
    have := congrArg norm h2
    rwa [norm_mul, norm_mul, hχ, mul_one, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
  have hN : (0 : ℝ) < Y.card := by
    rcases (Nat.eq_zero_or_pos Y.card) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at h3; exact absurd h3 hr.ne
    · exact_mod_cast h
  have h4 : r = Real.sqrt (Y.card : ℝ) := by
    rw [← h3]
    have : ‖lam‖ ^ 2 = (Y.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hN.le (by positivity),
      show ‖lam‖ * (Y.card : ℝ) * (‖lam‖ * Y.card) = ‖lam‖ ^ 2 * Y.card * Y.card by ring, this,
      inv_mul_cancel₀ hN.ne', one_mul]
  have hNc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold flipScal
  rw [← hcard]
  have hs : Real.sqrt (Y.card : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h5 : lam = r * ((χW x : Circle) : ℂ)⁻¹ / Y.card := by rw [← h2]; field_simp
  rw [h5, h4]
  have hsq : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) = Y.card := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hsc : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp
  rw [← hsq]
  ring

end GlobalTheory.FlipScal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedVacuumTranslateSumFlipScalarStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.movedVacuum_translateSum_flipScalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (x : (AE D)ˣ) (lam : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → Y.card = flipIdx V W T m → om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ → lam = flipScal χW V W T m x := by
  first | exact @GlobalTheory.FlipScal.moved_vacuum_factor | exact GlobalTheory.FlipScal.moved_vacuum_factor | (intros; apply GlobalTheory.FlipScal.moved_vacuum_factor <;> assumption)
end
end
