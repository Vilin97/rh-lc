module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionLevi
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_pair_restriction_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ t m, IsLevi (W₁ := W₁) H' t 1 m →
        ∀ k : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = k • e Φ) → (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
        (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) M.co dd →
        IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) dd χX (diagCols (Fin d)) omd →
        (∀ (g : UA σ W.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J))),
          (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat g) 0 0 1 →
          ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
        ∀ p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)),
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat m) 0 0 1 * GlobalTheory.DblUnip.unipMat (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ).toRingHom ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
        ∃ Λ : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
          (∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (dd.rho B.ψ (z * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = Λ φ) ∧
          (∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (omd p φ) = (k * (((absE F E t : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ)) * Λ φ) ∧
          ∃ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), Λ φ ≠ 0 := by
  first | exact @GlobalTheory.TorusLamP.exists_lam | exact GlobalTheory.TorusLamP.exists_lam | (intros; apply GlobalTheory.TorusLamP.exists_lam <;> assumption)
