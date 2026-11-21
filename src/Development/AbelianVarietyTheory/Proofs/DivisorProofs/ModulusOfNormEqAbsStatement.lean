module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_of_norm_eq_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) x) = absE F E x := by
  first | exact @GlobalTheory.ModuAdele.modu_norm_eq_absE | exact GlobalTheory.ModuAdele.modu_norm_eq_absE | (intros; apply GlobalTheory.ModuAdele.modu_norm_eq_absE <;> assumption)
