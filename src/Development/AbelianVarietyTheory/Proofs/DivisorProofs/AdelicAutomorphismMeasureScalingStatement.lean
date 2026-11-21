module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAutomorphismMeasureScaling
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_automorphism_measure_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (b : ℕ) (J₁ : Matrix (Fin b) (Fin b) E), J₁.det ≠ 0 → ∀ (l : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (g₀ : UA σ J₁)
    [IsTopologicalAddGroup (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] [LocallyCompactSpace (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] [MeasurableSpace (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]
    [BorelSpace (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] (A : (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≃ₜ+ (Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    (∀ a, A a = l.1 • ((mat g₀⁻¹)ᵀ *ᵥ a)) → addEquivAddHaarChar A = absE F E l ^ b := by
  first | exact @GlobalTheory.LeviModulus.modulus_levi | exact GlobalTheory.LeviModulus.modulus_levi | (intros; apply GlobalTheory.LeviModulus.modulus_levi <;> assumption)
