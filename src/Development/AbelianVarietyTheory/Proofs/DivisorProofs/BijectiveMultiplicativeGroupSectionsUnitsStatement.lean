module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec ℤ unitsF U) :=
  GlobalTheory.EtC.GmSec.gm_sec_bijective
