module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_adelic_lattice_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n), X.L.IsLattice E → IsClosed ((latHat X : AddSubgroup (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Set (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  first | exact @GlobalTheory.LatHatClosed.isClosed_latHat | exact GlobalTheory.LatHatClosed.isClosed_latHat | (intros; apply GlobalTheory.LatHatClosed.isClosed_latHat <;> assumption)
