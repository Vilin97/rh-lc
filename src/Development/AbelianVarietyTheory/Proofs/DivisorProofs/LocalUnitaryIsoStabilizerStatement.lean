module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryIsoStabilizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_iso_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (δ : E), δ ≠ 0 → W.L.FG →
    ∃ e : GlobalTheory.SphLine.locU σ W v ≃* GLoc σ (δ • W.J.map σ) v,
      ∀ g, g.1 ∈ GlobalTheory.SphLine.locK σ W v ↔ e g ∈ stabLoc σ (δ • W.J.map σ) W.L v := by
  first | exact @GlobalTheory.SphLineLoc.exists_locEquiv | exact GlobalTheory.SphLineLoc.exists_locEquiv | (intros; apply GlobalTheory.SphLineLoc.exists_locEquiv <;> assumption)
