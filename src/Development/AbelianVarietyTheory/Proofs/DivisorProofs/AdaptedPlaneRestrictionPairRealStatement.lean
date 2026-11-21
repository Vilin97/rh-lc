module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_restriction_pair_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (m : UA σ X.J), IsLevi (W₁ := X₁) H t 1 m →
      ∃ (Cy : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (md : UG (cA σ) (dbl (incM F X.J))) (T : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (g : UG (cA σ) (dbl (incM F X.J))) (S : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        (∀ z : Matrix (Fin d) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∃ (y₁ y₂ : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u : Matrix (Fin d) (Fin n₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
          z * Cyᵀ = Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H.x) + u * (incM F H.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H.x) + u * (incM F H.ι)ᵀ)) ∧
        ((md : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          Matrix.fromBlocks (mat m) 0 0 1 ∧
        ((md : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Cy = Cy * (T : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
        Matrix.GeneralLinearGroup.det T = t ∧
        ((g : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Cy =
          (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (S : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  first | exact @GlobalTheory.MixedPlane.exists_mixed_model | exact GlobalTheory.MixedPlane.exists_mixed_model | (intros; apply GlobalTheory.MixedPlane.exists_mixed_model <;> assumption)
