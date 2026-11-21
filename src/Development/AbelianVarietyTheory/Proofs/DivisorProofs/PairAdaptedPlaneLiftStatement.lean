module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_plane_lift : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₁.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₁.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₁.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d₁' dd₁ →
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ μ₁ : @Measure ((Fin n × Fin d₁) → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ₁ →
      ∀ μ : @Measure (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      ∀ g ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → FiniteAdeleRing (𝓞 F) F),
        ∃ T : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
          ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ,
            (letI : MeasurableSpace (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := borel _; Integrable (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)))) μ) ∧
            (letI : MeasurableSpace (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := borel _; ∫ y, GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g))) ∂μ) = T f := by
  first | exact @GlobalTheory.SiegelAvgCore.main | exact GlobalTheory.SiegelAvgCore.main | (intros; apply GlobalTheory.SiegelAvgCore.main <;> assumption)
