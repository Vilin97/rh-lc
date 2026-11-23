module

public import Development.WeilBound.ThetaLifts.CTKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ThetaTowerHermitianSecondHolds
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairRestrictionStatement
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegral
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairLocalFactor

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_local_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J), ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  first | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairSeesawIdentity

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_seesaw_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H t g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  first | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegralStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_theta_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  first | exact @GlobalTheory.MixXUnip.unip_trivial_m | exact fun _ => @GlobalTheory.MixXUnip.unip_trivial_m | exact GlobalTheory.MixXUnip.unip_trivial_m | exact @GlobalTheory.MixXUnip.unip_trivial_m trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlaneFirstVariable

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKMixX

theorem mixed_model_plane_X_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      (∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e) ∧
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ h t g₁ m, IsLevi H t g₁ m → ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (u * m, h) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, h) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  refine ⟨PositivityTheory.Mix.T.adapted_plane_pair_restriction F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁, ?_⟩
  intro e he h t g₁ m hm u hu Φ hΦ
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    fun x Φ hΦ => hP.weil.isUSplitting.pres x Φ hΦ
  have hsplit : ((u * m, h) : UA σ X.J × UA σ W.J) = ((u, 1) * (m, 1)) * (1, h) := by simp
  rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    PositivityTheory.Mix.T.adapted_plane_pair_theta_integral F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu _ (pres _ _ (pres _ _ hΦ)),
    PositivityTheory.Mix.T.adapted_plane_pair_seesaw_identity F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t g₁ m hm _ (pres _ _ hΦ),
    PositivityTheory.Mix.T.adapted_plane_pair_local_factor F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h Φ hΦ,
    ← Module.End.mul_apply, ← map_mul]
  simp

end GlobalTheory.ThKMixX
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixXClosed

section

@[expose] public section

theorem PositivityTheory.Mix.mixX_closed : PositivityTheory.ThKG.MixX := GlobalTheory.ThKMixX.mixed_model_plane_X_m
end
end
