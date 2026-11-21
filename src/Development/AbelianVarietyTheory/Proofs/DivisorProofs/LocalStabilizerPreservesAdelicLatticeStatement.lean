module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerPreservesAdelicLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stabilizer_preserves_adelic_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Spc F E n) (v : Pl (F := F)), ∀ k ∈ stabLoc σ J X.L v,
      ∀ z ∈ latHat X, (HA.mat (AF F) σ J (emb σ J v k) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ latHat X := by
  first | exact @GlobalTheory.LatHatStab.mulVec_mem_latHat | exact GlobalTheory.LatHatStab.mulVec_mem_latHat | (intros; apply GlobalTheory.LatHatStab.mulVec_mem_latHat <;> assumption)
