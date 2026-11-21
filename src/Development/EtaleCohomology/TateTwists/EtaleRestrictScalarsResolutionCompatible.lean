module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S)
    (U : Scheme.{0}) (a : Sec F U),
    (restrMap φ F).app U 0 (Sec.map (resι S F) a) =
      Sec.map (resι R ((restr R φ).obj F)) (show Sec ((restr R φ).obj F) U from a)
