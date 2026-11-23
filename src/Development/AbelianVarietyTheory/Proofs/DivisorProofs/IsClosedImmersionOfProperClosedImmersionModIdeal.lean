module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericallyFiniteFiniteNearCodimOnePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdeal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem fibre_subsingleton_of_isClosedImmersion_restrict :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
      (p : Z ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) →
      ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  intro R _ I X Z φ p hci z hz
  have hmem : ∀ x : X, φ x = z → x ∈ Set.range ((baseIdeal p I).comap φ).subschemeι := by
    intro x hx
    rw [Scheme.IdealSheafData.range_subschemeι, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R Z X p φ I]
    show x ∈ (baseIdeal (φ ≫ p) I).support
    refine (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R X (φ ≫ p) I x).mpr ?_
    have e : (φ ≫ p) x = p (φ x) := by simp
    rw [e, hx]
    exact hz
  intro x hx x' hx'
  obtain ⟨y, rfl⟩ := hmem x hx
  obtain ⟨y', rfl⟩ := hmem x' hx'
  have hinj := (((baseIdeal p I).comap φ).subschemeι ≫ φ).isClosedEmbedding.injective
  have : y = y' := hinj (by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    have e : ∀ w, (((baseIdeal p I).comap φ).subschemeι ≫ φ) w = φ (((baseIdeal p I).comap φ).subschemeι w) := fun w => by simp
    rw [e, e, hx, hx'])
  rw [this]

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdealStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  first | exact @GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | exact GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | (intros; apply GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestriStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) → IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | exact GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | (intros; apply GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheaf

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem mem_basicOpen_of_sub_one_mem_baseIdeal (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0})
    (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z)
    (hz : z ∈ V) (hI : I ≤ (p z).asIdeal) (hr : r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩) :
    z ∈ Z.basicOpen r := by
  have hs : z ∈ (baseIdeal p I).support := (mem_support_baseIdeal p I z).2 hI
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hz] at hs
  have h1 : z ∉ Z.basicOpen (r - 1) := by
    rw [Scheme.mem_zeroLocus_iff] at hs
    exact hs _ hr
  rw [Scheme.mem_basicOpen _ _ _ hz] at h1 ⊢
  have hsum : Z.presheaf.germ V z hz r + (-(Z.presheaf.germ V z hz (r - 1))) = 1 := by
    simp [map_sub]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact h
  · exact absurd (by simpa using h.neg) h1

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheafStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf : ∀ (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0}) (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z), z ∈ V → I ≤ (p z).asIdeal → r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩ → z ∈ Z.basicOpen r := by
  first | exact @GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | exact GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | (intros; apply GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSectionsModBaseIdealOfClosedImmersion

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem surj_mod_baseIdeal_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  intro R _ I X Z φ p hg V hV hW
  set K := (baseIdeal p I).comap φ with hK
  have hKid : K.ideal ⟨φ ⁻¹ᵁ V, hW⟩ = ((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom := by
    rw [hK, GlobalTheory.Principalise.comapIdealAffine (baseIdeal p I) φ ⟨V, hV⟩ ⟨φ ⁻¹ᵁ V, hW⟩ le_rfl,
      Scheme.Hom.app_eq_appLE]
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective (K.subschemeι ≫ φ) V hV
    ((K.subschemeι.app (φ ⁻¹ᵁ V)).hom c)
  refine ⟨b, ?_⟩
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, ← hKid, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub]
  rw [Scheme.Hom.comp_app] at hb
  rw [sub_eq_zero]
  exact hb

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSectionsModBaseIdealOfClosedImmersionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  first | exact @GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | exact GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdeal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.ClosedLev

theorem exists_nhd (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
    (p : Z ⟶ Spec (CommRingCat.of R)) (hφ : IsProper φ)
    (hc : IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ)) (z : Z)
    (hz : I ≤ (p z).asIdeal) : ∃ U : Z.Opens, z ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
  have hfin : (⇑φ ⁻¹' {z}).Finite := (GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal R I X Z φ p hc z hz).finite
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ z hfin
  obtain ⟨V, hV, hzV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hzV₀
  have hVf : IsFinite (φ ∣_ V) := GlobalTheory.PushFinite.isFinite_restrict_of_le φ hle
  obtain ⟨haff, hfr⟩ := GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite X Z φ V hV hVf
  obtain ⟨r, hr1, hr⟩ := GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod _ _ (φ.app V).hom hfr _ (GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion R I X Z φ p hc V hV haff)
  exact ⟨Z.basicOpen r, GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf R I Z p V hV r z hzV hz hr1, GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range X Z φ V hV haff r hr⟩

theorem isClosedImmersion_of_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  intro R _ I hI X Z φ p hφ hp hc
  let O : Z.Opens := ⨆ U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)}, U.1
  have hO : O = ⊤ := by
    have h0 := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI Z p hp ((O : Set Z)ᶜ) O.isOpen.isClosed_compl fun z hz hIz => by
      obtain ⟨U, hzU, hU⟩ := exists_nhd R I X Z φ p hφ hc z hIz
      exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩)
    exact TopologicalSpace.Opens.ext (by simpa [Set.compl_empty_iff] using h0)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)} => U.1) hO fun U => U.2

end GlobalTheory.ClosedLev
end
end
