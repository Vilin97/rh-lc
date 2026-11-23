module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledLatticeLocalImageFullAtInertPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSpStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigen

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen

theorem local_identity_of_tens_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f R c hγ hR x₀ hx₀ hA ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : R x = R x₀ := hR x₀ z hzat
  have hrx1 : R (x + (co.e γ).1) = R x := hR x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b

    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : R x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  apply mul_right_cancel₀ hr0
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
  linear_combination this

end GlobalTheory.DblVacEigen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigenStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  first | exact @GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | exact GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | (intros; apply GlobalTheory.DblVacEigen.local_identity_of_tens_eigen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen.SympAct

theorem hTens_eq_mat {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_actB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E) : symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  have key : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB

    rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E).map c)ᵀ by
    ext i j; simp [Matrix.mul_apply, map_sum, map_mul]]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc x * ((g : GL β E) : Matrix β β E)ᵀ * JB * (((g : GL β E) : Matrix β β E).map c * (y.map c)ᵀ)
        = x * (((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c) * (y.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_mat, hTens_eq_mat, key]

end GlobalTheory.DblVacEigen.SympAct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariantStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant : ∀ {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E), symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  first | exact @GlobalTheory.DblVacEigen.SympAct.symp_actB | exact GlobalTheory.DblVacEigen.SympAct.symp_actB | (intros; apply GlobalTheory.DblVacEigen.SympAct.symp_actB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerScalesDoubledVacuum

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen

open MeasureTheory

theorem sb_boxFun {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_star {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) : (fun x => star (φ x)) ∈ SB X :=
  ⟨h.1.comp (fun z : ℂ => star z), h.2.comp_left (g := fun z : ℂ => star z) (star_zero _)⟩

theorem locality_op {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) (hkeep : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) :
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ, ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB _ ∧ Acts (evFin F v) T φ (S φ) := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    have e1 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (u • p, u • (0 : κ → AF F)) Ψ = fun y => Ψ (y + u • p) := fun Ψ => by
      funext y; simp [schr]
    rw [e1, e1] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨fun φ t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp
    ring

end GlobalTheory.DblVacEigen

noncomputable section
namespace GlobalTheory.DblVacEigen

theorem eigen_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr g hg
  classical
  by_cases hr0 : ∀ x, r x = 0
  · refine ⟨0, ?_⟩
    have h0 : boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) = 0 := by
      funext x; simp [boxFun, tens, hr0]
    rw [h0, map_zero, smul_zero]
  push_neg at hr0
  obtain ⟨x₀, hx₀⟩ := hr0
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hψ1 : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hT.base.std
  set vac := G.M.vac v with hvacdef
  set V₀ := tens (evFin F v) vac r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  set vd : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ := boxFun vac (fun x => star (vac x)) with hvd
  set R : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ := boxFun r (fun x => star (r x)) with hR
  have hSt : S = tens (evFin F v) vd R := by
    funext x
    simp only [hS, hvd, hR, hV₀, boxFun, tens, star_mul', Function.comp_def]
    ring
  have hSA : S ∈ schA F _ := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ V₀ hr.2 _ (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hRinv : ∀ x z, At (evFin F v) z → R (x + z) = R x := by
    intro x z hz
    have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hr' : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inr i)
    simp only [hR, boxFun]
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hl, hr.1 _ _ hr']
  have hRest : Rest (evFin F v) vd R := ⟨hRinv, hSt ▸ hSA⟩
  have hvdSB : vd ∈ SB _ := sb_boxFun hvSB (sb_star hvSB)
  have hvd0 : vd ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hv0
    intro h
    have h1 := congrFun h (Sum.elim y y)
    simp only [hvd, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at h1 hy
    exact mul_ne_zero hy (star_ne_zero.mpr hy) h1
  have hRx : R (Sum.elim x₀ x₀) ≠ 0 := by
    simp only [hR, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)

  have hspl := hsp.2.1
  have hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F,
      ∀ Φ ∈ schA F _, omd g (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (omd g Φ) := by
    intro u hu p q Φ hΦ
    set w' := dd.e.symm (p, q) with hw'
    have he : dd.e (u • w') = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h0 : u • (GlobalTheory.DblVac.matD g - 1) = 0 := hg.1 u hu
    have hact : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (u • w') = u • w' := by
      have h1 : (u • w') * (GlobalTheory.DblVac.matD g)ᵀ - u • w' = w' * (u • (GlobalTheory.DblVac.matD g - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
      exact h1
    have h2 := hspl.impl g (u • w') Φ hΦ
    simp only [Darboux.rho] at h2
    set_option backward.isDefEq.respectTransparency false in
      rw [hact, he] at h2
    exact h2
  obtain ⟨Tl, hTl⟩ := locality_op v B.ψ (omd g) hT.base.std (fun Φ hΦ => hspl.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hspl.unit μ hμ g Φ hΦ) hcomm
  have hgS : omd g S = tens (evFin F v) (Tl vd) R := by rw [hSt]; exact (hTl vd hvdSB).2 R hRest

  have hV₀eig : ∀ γ ∈ (latAtV G.V G.W v : Set _), G.M.co.rho B.ψ γ V₀ =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • V₀ := by
    intro γ hγ
    rw [hV₀, hvac γ hγ r hr]
    funext x
    set_option backward.isDefEq.respectTransparency false in
      simp [tens, mul_assoc, cA, incM]
  have hSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ S =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) γ γ) • S :=
    fun γ hγ => GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) (inclR (F := F) (AF F) (θ : E)) _ _ G.M.co dd hdc B.ψ hψ1 _ V₀ hV₀eig γ hγ.1 hγ.2

  have hgSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (omd g S) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) γ γ) • omd g S := by
    intro γ hγ
    have hK := (GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice F E σ G.V G.W v g hg γ hγ).2
    have h1 := hspl.impl g (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g⁻¹ γ) S hSA
    have h2 : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g⁻¹ γ) = γ := by
      simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
      have e : ((g : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) *
          (((g⁻¹ : GlobalTheory.DblVac.UD σ G.W) : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      set_option backward.isDefEq.respectTransparency false in
        rw [e, Matrix.transpose_one, Matrix.mul_one]
    set_option backward.isDefEq.respectTransparency false in
      rw [h2] at h1
    refine h1.symm.trans ?_
    set_option backward.isDefEq.respectTransparency false in
      rw [hSeig (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g⁻¹ γ) hK, map_smul, GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant]
    rfl

  let Λd := (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v)
  let χ : (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) × ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v)) → ℂ :=
    fun l => if h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l then
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) h.choose h.choose)
      else 0
  have loc : ∀ f : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ,
      (∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (tens (evFin F v) f R) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) γ γ) •
          tens (evFin F v) f R) →
      ∀ l ∈ Λd, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l := AddSubgroup.mem_map.mp hl
    have key := GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen v dd B.ψ h.choose f R _ (at_of_mem_latDbl _ _ _ h.choose_spec.1) hRinv
      (Sum.elim x₀ x₀) hRx (hf _ h.choose_spec.1) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  have hloc1 := loc vd (fun γ hγ => hSt ▸ hSeig γ hγ)
  have hloc2 := loc (Tl vd) (fun γ hγ => hgS ▸ hgSeig γ hγ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergEigen_proportional_localField (GlobalTheory.LatVac.psiAt B.ψ v) Λd χ vd (Tl vd) hloc1 hloc2 hvd0
    (GlobalTheory.T.doubled_lattice_local_image_full_at_inert_place F E σ B a a' G X om om' hT v w hw dd hdc)
  refine ⟨c, ?_⟩
  rw [hgS, hc, hSt]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.DblVacEigen
end
end
end
end
