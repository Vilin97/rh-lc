module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLeviDecompositionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_levi_decomposition_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl (F := F),
    ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (h₁ : UA σ W₁.J), At (evFin F v) ((t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) → h₁ ∈ UAt σ W₁ (evFin F v) →
    ∃ m : UA σ W.J, IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) := by
  first | exact @GlobalTheory.PlaneLeviUnit.levi_unit_at | exact GlobalTheory.PlaneLeviUnit.levi_unit_at | (intros; apply GlobalTheory.PlaneLeviUnit.levi_unit_at <;> assumption)
