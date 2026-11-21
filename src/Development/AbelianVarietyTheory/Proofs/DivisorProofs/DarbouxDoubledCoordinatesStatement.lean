module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDoubledCoordinates
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairTransferAlongPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_doubled_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ d r' s' : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d)
    (M : Model σ X W) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → W.IsSkew σ B r' s' →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) M.co dd →
    ∀ u : Fin d → E, (∀ z : Fin d → E,
      (dd.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).1 ⬝ᵥ (dd.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (Matrix.vecMulVec H.x (Sum.elim z 0)))).2 =
        (dd.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (Matrix.vecMulVec H.x (Sum.elim z 0)))).1 ⬝ᵥ (dd.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).2) →
    u = 0 := by
  first | exact @GlobalTheory.DblLagrNondeg.nondeg | exact GlobalTheory.DblLagrNondeg.nondeg | (intros; apply GlobalTheory.DblLagrNondeg.nondeg <;> assumption)
