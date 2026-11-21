module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerIsOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_stabilizer_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsOpen ((GlobalTheory.IdeleTate.stab F E : Subgroup (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) := by
  first | exact @GlobalTheory.IdeleTate.isOpen_stab | exact GlobalTheory.IdeleTate.isOpen_stab | (intros; apply GlobalTheory.IdeleTate.isOpen_stab <;> assumption)
