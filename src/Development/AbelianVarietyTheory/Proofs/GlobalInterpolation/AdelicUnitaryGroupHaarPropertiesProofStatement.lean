module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlac

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  first | exact @GlobalTheory.AdelicStabUnimod.unimodularOver_adele | exact GlobalTheory.AdelicStabUnimod.unimodularOver_adele | (intros; apply GlobalTheory.AdelicStabUnimod.unimodularOver_adele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodularStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Ainf F) σ J := by
  first | exact @GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | (intros; apply GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVectorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  first | exact @GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | exact GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | (intros; apply GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlacStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  first | exact @GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | exact GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | (intros; apply GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  first | exact @GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | (intros; apply GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof

section

@[expose] public section

namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProofStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)
end
end
