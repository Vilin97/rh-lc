module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHomsStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActOFIotaVFEqIotaVFMulVec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianVector
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartThetaEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinates
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormMatrixSelfadjoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaOfSmFK

section

@[expose] public section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.ThetaOfSmF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.ThetaOfSmF
open GlobalTheory.ThetaOfSmF in
theorem GlobalTheory.ThetaOfSmF.theta_of_smF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB)
  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add (f := _), Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _
  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _), neg_add] }
  have hφ : Continuous φ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) := by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianInvariant

section

@[expose] public section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  first | exact @_root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k | exact _root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k | (intros; apply _root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousMMFK

section

@[expose] public section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealWeilF.MCont
theorem continuous_mMF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2
end GlobalTheory.RealWeilF.MCont
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousMomentMap

section

@[expose] public section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.continuous_moment_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  first | exact @_root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k | exact _root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k | (intros; apply _root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutRealA

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem exists_inf_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  have hB := C.good
  have hc : IsCharAF F B.ψ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).1
  have hθ := C.inf
  have hι := C.chart
  have hS := C.hS
  have hT := C.hT
  have hξ := C.h0
  have hξσ := C.hξ
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ
  have hHeis : IsHeis (fun x y => (star y ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => norm_rhoBF hc _ f, fun f => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι 0) f = f
      rw [iotaVF_zero, rhoBF_zero]
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) f) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι (u + v)) f
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hι)
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (IxF F nS nT) (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)) hH.1 hH.2
      (BBF σ JS JT ξ₀ B.ψ) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hHeis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
      (_root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι)
  have sm := _root_.GlobalTheory.T.archimedean_chart_gaussian_norm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc
  have hfr := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀
  have rcomm : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) =
        rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, (hfr u _ hu (real_iotaVF hι v)).2, add_comm]
  have radd : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc (u + iotaVF ι v) f = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, AddChar.map_zero_eq_one, one_smul]
  have hfin : ∀ p {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ f : BBF σ JS JT ξ₀ B.ψ,
      Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) f → Ω p (rhoBF σ JS JT ξ₀ B.ψ hc u f) = rhoBF σ JS JT ξ₀ B.ψ hc u (Ω p f) :=
    fun p u hu f hf => hcomm p _ (fun v g => rcomm hu v g) f hf
  have hth : ∀ p (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 → IsThetaFunOF σ JS JT ξ₀ B.ψ (Ω p f).1 := by
    intro p f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc _ (hsm p f (sm f hf)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoBF σ JS JT ξ₀ B.ψ hc u f = f := QB_ext fun x => congrFun ((coe_rhoBF hc u f).trans (hl u hu h0)) x
    rw [← coe_rhoBF hc, ← hfin p h0 f (sm f hf), e]
  have hbd := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc
  obtain ⟨om, hom⟩ := exists_homF hbd Ω hth (fun p f f' h1 h2 => hadd p f f' (sm f h1) (sm f' h2))
    (fun p a f h1 => hsmul p a f (sm f h1)) (fun f h1 => hone f (sm f h1)) fun p p' f h1 => hmul p p' f (sm f h1)
  have lift : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ G : BBF σ JS JT ξ₀ B.ψ, (G.1 : WOF F E nS nT → ℂ) = f :=
    fun f hf => ⟨toBF f hf.cont (hbd f hf) hf.quasi, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_⟩, fun s hs hpos p hsc f hf hv => ?_⟩ <;> obtain ⟨G, rfl⟩ := lift f hf
  · rw [hom p G hf]
    exact hth p G hf
  · simp only [hom _ G hf]
    exact (ev _ _ w).continuous.comp
      (hcont (_root_.GlobalTheory.T.continuous_moment_map F E σ B hB nS nT JS JT θ hθ) G (sm G hf))
  · rw [hom p G hf]
    exact GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 _ _
      fun H _ _ _ Φ hΦ => hunit H Φ (fun v g => hΦ _ g) p G (sm G hf)
  · rw [hom _ G hf, htriv _ (mMF_fin θ hg hk) G (sm G hf)]
  · obtain ⟨u, v, hu, rfl⟩ := GlobalTheory.T.exists_finiteAdelic_add_realChartPoint F E nS nT θ ι hι w
    have h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoVF σ JS JT ξ₀ B.ψ hc ι v G).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ hf
    have h2 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v G)).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ h1
    have e1 : actOF σ JS JT g k (u + iotaVF ι v) = u + iotaVF ι (mMF σ JS JT θ (g, k) *ᵥ v) := by
      rw [GlobalTheory.RealWeilF.actOF_add, GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms F E σ nS nT JS JT g k hg hk u hu, _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    rw [hom _ G hf, e1, ← coe_rhoBF hc _ G, ← coe_rhoBF hc _ (Ω (g, k) G), radd hu v G,
      radd hu _ (Ω (g, k) G), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm G hf)]
  · rw [hom _ G hf, hvac s p hs hpos hsc G (sm G hf) (fderiv_vacF hc ι s G (sm G hf) hv)]
    rfl
end PositivityTheory.ThKW
end
end
end
end
