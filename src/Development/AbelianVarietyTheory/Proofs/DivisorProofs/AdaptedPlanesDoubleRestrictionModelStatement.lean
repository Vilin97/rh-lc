module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesDoubleRestrictionModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_planes_double_restriction_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d))
      (eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ z, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H.ι * z * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2)) ∧
      (∀ u ∈ isoA H H', (co.e u).1 = 0 ∧ ∀ j, (co.e u).2 (eq.symm (Sum.inr j)) = 0) ∧
      ∀ u ∈ isoAd H H', (co.e u).2 = 0 ∧ ∀ j, (co.e u).1 (eq.symm (Sum.inr j)) = 0 := by
  first | exact @GlobalTheory.TwoPlanes.exists_adapted_coords | exact GlobalTheory.TwoPlanes.exists_adapted_coords | (intros; apply GlobalTheory.TwoPlanes.exists_adapted_coords <;> assumption)
