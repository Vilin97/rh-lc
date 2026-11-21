module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_trace_basis_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Fin n → E) (x' y' : Fin d → E),
    form σ J x y = 1 → form σ J' y' x' = -1 → ∃ t : Fin (Module.finrank F E) → E, ∀ i j,
      symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J')
        (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F x) (incV F y'))
        (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F y) (incV F x')) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.ArchDualPair.dualPair | exact GlobalTheory.ArchDualPair.dualPair | (intros; apply GlobalTheory.ArchDualPair.dualPair <;> assumption)
