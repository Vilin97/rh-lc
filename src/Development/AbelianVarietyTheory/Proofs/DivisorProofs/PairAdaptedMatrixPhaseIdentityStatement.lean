module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedMatrixPhaseIdentity
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_matrix_phase_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Z Z' : Matrix (Fin d₁) (Fin n) (AE F E)) (Y Y' : Fin n ⊕ Fin n → AE F E),
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y)
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H'.ι * (Z' * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y') = 0 := by
  first | exact @GlobalTheory.SiegelIsotr.isotropic_mixed | exact GlobalTheory.SiegelIsotr.isotropic_mixed | (intros; apply GlobalTheory.SiegelIsotr.isotropic_mixed <;> assumption)
