module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneAd
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
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.UnitaryFixingVectorPreserves
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsUnitaryScalingIsotropic

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.Mix

theorem PositivityTheory.Mix.exists_unitary_scaling_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hH hX _ t ht
  obtain ⟨ε, h⟩ := planeOK_herm hB hH hX
  exact exists_scale h t ht
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsUnitaryScalingVector

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.exists_unitary_scaling_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  first | exact @PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact fun _ => @PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact @PositivityTheory.Mix.exists_unitary_scaling_isotropic trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPairConverse

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_pair_converse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact fun _ => @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral trivial
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairOfPair

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnip

theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add (f := _)]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (q : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

end GlobalTheory.MixXUnip
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPairOfPair

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_pair_of_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  first | exact @GlobalTheory.MixXUnip.twist_heis_inv | exact fun _ => @GlobalTheory.MixXUnip.twist_heis_inv | exact GlobalTheory.MixXUnip.twist_heis_inv | exact @GlobalTheory.MixXUnip.twist_heis_inv trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPlaneLocal

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_plane_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction trivial
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegral

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXUnip

theorem unip_trivial_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu
  have hS := IsUWeilPair.isUSplitting hP.weil
  have pres : ∀ g Φ, Φ ∈ schA F (Fin n × Fin d) → om g Φ ∈ schA F (Fin n × Fin d) := fun g Φ h => hS.pres g Φ h
  have omul : ∀ g h : UA σ X.J, ∀ Φ, om (g * h, 1) Φ = om (g, 1) (om (h, 1) Φ) := fun g h Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have om1 : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have twist : ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ := by
    intro g a ha hb
    obtain ⟨h1, h2⟩ := PositivityTheory.Mix.T.hermitian_adapted_pair_of_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a ha hb
    refine PositivityTheory.Mix.T.hermitian_adapted_plane_local F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
      (e ∘ₗ om (g, 1)) h1 h2 fun y => ?_
    have := hS.adm (g, 1) _ (PositivityTheory.Mix.T.hermitian_adapted_pair_converse F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he y)
    rwa [LinearMap.comp_assoc] at this
  by_cases h0 : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = 0
  · intro Φ hΦ
    rw [h0 _ (pres _ _ hΦ), h0 _ hΦ]
  push_neg at h0
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  let Q : UA σ X.J → ℂ → Prop := fun g c => ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ
  have Quniq : ∀ g c c', Q g c → Q g c' → c = c' := fun g c c' h h' =>
    smul_left_injective ℂ hne ((h Φ₀ hΦ₀).symm.trans (h' Φ₀ hΦ₀))
  have Qmul : ∀ g h c c', Q g c → Q h c' → Q (g * h) (c * c') := fun g h c c' hg hh Φ hΦ => by
    rw [omul, hg _ (pres _ _ hΦ), hh _ hΦ, smul_smul]
  have Qone : Q 1 1 := fun Φ _ => by rw [om1, one_smul]
  have Qinv : ∀ g c, Q g c → c ≠ 0 ∧ Q g⁻¹ c⁻¹ := by
    intro g c hg
    have key : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = c • e (om (g⁻¹, 1) Φ) := fun Φ hΦ => by
      rw [← hg _ (pres _ _ hΦ), ← omul, mul_inv_cancel, om1]
    have hc : c ≠ 0 := fun h => hne (by rw [key _ hΦ₀, h, zero_smul])
    exact ⟨hc, fun Φ hΦ => by rw [key Φ hΦ, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have Qpow : ∀ g c, Q g c → ∀ k : ℕ, Q (g ^ k) (c ^ k) := by
    intro g c hg k
    induction k with
    | zero => simpa using Qone
    | succ k ih => rw [pow_succ, pow_succ]; exact Qmul _ _ _ _ ih hg

  have gen : ∀ g : UA σ X.J, mat g *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) → Q g 1 := by
    intro g hgx hgz
    obtain ⟨cu, hcu⟩ := twist g 1 (by rw [one_smul]; exact hgx) hgz
    have scl : ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, (mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) ∧
        ∃ c, Q m c := by
      intro t ht
      obtain ⟨m, h1, h2, h3⟩ := PositivityTheory.Mix.T.exists_unitary_scaling_vector F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hH hP.herm hP₁.herm t ht
      exact ⟨m, ⟨h1, h2, h3⟩, twist m _ h1 fun z => ⟨0, by rw [zero_smul, add_zero, h3]⟩⟩
    obtain ⟨m, ⟨hm1, hm2, hm3⟩, cm, hcm⟩ := scl 2 two_ne_zero
    have hm1' : mat m *ᵥ incV F H.x = (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x := by exact_mod_cast hm1
    have hm2' : (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y := by exact_mod_cast hm2
    obtain ⟨hcm0, hcmi⟩ := Qinv _ _ hcm
    obtain ⟨hcu0, hcui⟩ := Qinv _ _ hcu
    set v := g⁻¹ * g⁻¹ * (m * g * m⁻¹) with hv
    have hQv : Q v (cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹)) :=
      Qmul _ _ _ _ (Qmul _ _ _ _ hcui hcui) (Qmul _ _ _ _ (Qmul _ _ _ _ hcm hcu) hcmi)
    set cv := cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹) with hcv
    have hcv' : cv = cu⁻¹ := by rw [hcv]; field_simp
    have step : ∀ t : ℕ, t ≠ 0 → cv ^ (t ^ 2) = cv := by
      intro t ht
      obtain ⟨m', ⟨h1, h2, h3⟩, cm', hcm'⟩ := scl t ht
      obtain ⟨hcm0', hcmi'⟩ := Qinv _ _ hcm'
      have e1 := Qmul _ _ _ _ (Qmul _ _ _ _ hcm' hQv) hcmi'
      rw [PositivityTheory.Mix.T.unitary_fixing_vector_preserves F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hH hP.herm hP₁.herm g hgx hgz m m' t hm1' hm2' hm3 h1 h2 h3] at e1
      have := Quniq _ _ _ (Qpow _ _ hQv (t ^ 2)) e1
      rw [this]; field_simp
    have hcv0 : cv ≠ 0 := by rw [hcv']; exact inv_ne_zero hcu0
    have s2 := step 2 two_ne_zero
    have s3 := step 3 three_ne_zero
    norm_num at s2 s3
    have c3 : cv ^ 3 = 1 := by
      have : cv * (cv ^ 3 - 1) = 0 := by linear_combination s2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hcv0)
    have c1 : cv = 1 := by rw [← s3, show 9 = 3 * 3 from rfl, pow_mul, c3, one_pow]
    have : cu = 1 := by rw [hcv', inv_eq_one] at c1; exact c1
    rw [← this]; exact hcu

  have hcl : ∀ g ∈ unip σ X H, Q g 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact gen g hg.1 hg.2
    | one => exact Qone
    | mul g h _ _ ihg ihh => simpa using Qmul _ _ _ _ ihg ihh
    | inv g _ ih => simpa using (Qinv _ _ ih).2
  intro Φ hΦ
  simpa using hcl u hu Φ hΦ

end GlobalTheory.MixXUnip
end
end
