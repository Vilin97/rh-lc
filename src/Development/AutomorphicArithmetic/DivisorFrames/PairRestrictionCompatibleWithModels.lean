module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
public import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSmulLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

private theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) : co.rho ψ 0 Φ = Φ := by
  funext z
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

private theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  apply invOf_eq_right_inv
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num
