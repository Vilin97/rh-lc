module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialsInclusionLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polynomials_inclusion_le : ∀ (P Q R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (x : ℚ),
    (harmTy P Q R S x).map (polIncl P Q r₀ s₀).toLinearMap ≤ harmTy P Q (R + 1) (S + 1) x := by
  first | exact @GlobalTheory.FockInclHarm.harmTy_map_polIncl_le | exact GlobalTheory.FockInclHarm.harmTy_map_polIncl_le | (intros; apply GlobalTheory.FockInclHarm.harmTy_map_polIncl_le <;> assumption)
