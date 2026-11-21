module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecaySizeArchimedeanUnitInvariant
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
theorem _root_.GlobalTheory.T.idele_decay_size_archimedean_unit_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (b h : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ),
    (∀ w, GlobalTheory.Doubling.unitInf F E w b = 1) → GlobalTheory.IdeleDecay.size F E (b * h : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ).1 = GlobalTheory.IdeleDecay.size F E h.1 := by
  first | exact @GlobalTheory.IdeleSizeUnit.size_mul_of_unitInf_eq_one | exact GlobalTheory.IdeleSizeUnit.size_mul_of_unitInf_eq_one | (intros; apply GlobalTheory.IdeleSizeUnit.size_mul_of_unitInf_eq_one <;> assumption)
