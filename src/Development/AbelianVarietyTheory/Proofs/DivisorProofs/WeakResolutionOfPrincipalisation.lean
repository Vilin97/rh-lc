module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimTStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGenericStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartierStatement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpenStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.effCartier_comap_of_isIso_restrict_open : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  first | exact @GlobalTheory.effCartier_comap_of_isIso_restrict | exact GlobalTheory.effCartier_comap_of_isIso_restrict | (intros; apply GlobalTheory.effCartier_comap_of_isIso_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverFieldStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z, ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧ z ∈ Set.range j := by
  first | exact @GlobalTheory.exists_clopen_integral_of_smooth_over_field | exact GlobalTheory.exists_clopen_integral_of_smooth_over_field | (intros; apply GlobalTheory.exists_clopen_integral_of_smooth_over_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.RelDimOfDim

theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq :
    ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ),
      Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  intro F _ X _ q n hq hn
  have x₀ : X := Classical.arbitrary X
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected q x₀
  have h := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q d hd
  rw [hn] at h
  have hdn : d = n := by exact_mod_cast h.symm
  exact hdn ▸ hd

end GlobalTheory.RelDimOfDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ), Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  first | exact @GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | exact GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | (intros; apply GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' : ∀ (F : Type) [Field F] (W W' : Scheme.{0}) [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W), LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens, (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  first | exact @GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | exact GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | (intros; apply GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation

section

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.WeakRes

theorem isProjOver_comp_closed {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem isProjOver_seq {F : Type} [Field F] {Y Y' : Scheme.{0}} (f : Y ⟶ Sp F) {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) (hf : IsProjOver f) : IsProjOver (s ≫ f) := by
  induction h with
  | id => simpa using hf
  | @step Y₁ Y₂ s J π _ _ _ hb ih =>
    obtain ⟨X', b, hb', hproj, -⟩ := ProjBlowup.exists_blowup (s ≫ f) ih J
    obtain ⟨e, he, heb⟩ := ProjBlowup.exists_iso_of_blowup J π b hb hb'
    rw [← heb, Category.assoc]
    exact isProjOver_comp_closed e hproj


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem weak_resolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  intro hP F _ _ W _ p n hp hdim
  obtain ⟨N, i₀, hi₀, hi₀p⟩ := hp
  obtain ⟨ℓ, hℓ, hℓs, hℓd⟩ := GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo F N
  let i := i₀ ≫ ℓ
  let f := PSpace.str F (N + 2)
  have hif : i ≫ f = p := by simp [i, f, hℓs, hi₀p]
  have hsmf : SmoothOfRelativeDimension (N + 2) f := Adelic.smoothOfRelativeDimension_pspace F _
  have : Smooth f := by haveI := hsmf; exact SmoothOfRelativeDimension.smooth (N + 2) f
  have : IsLocallyNoetherian (PSpace F (N + 2)) := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hne, hnc⟩ := GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim i (hℓd _)
  obtain ⟨Y', s, -, -, -, hseq, -, hE, -⟩ := hP F (N + 2) _ f inferInstance hsmf
    (ProjSpace.isProjOver_pspace_str F _) i.ker hne
  rcases GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over f _ (i (genericPoint W)) s hseq with ⟨U, hU, hiso⟩ |
    ⟨Y₁, s₁, J, U, y₁, hseq₁, hsm, hJB, hU, hiso, hy₁, hs₁⟩
  · exact (hnc U hU (GlobalTheory.T.effCartier_comap_of_isIso_restrict_open s _ U hiso hE)).elim
  · obtain ⟨z, hz⟩ : ∃ z, J.subschemeι z = y₁ := by
      rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]; exact hy₁
    obtain ⟨W', j, hjc, hjo, hW', w', rfl⟩ := GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' F J.subscheme (J.subschemeι ≫ s₁ ≫ f) hsm z
    have hg : ∀ w, (j ≫ J.subschemeι ≫ s₁) w ∈ i.ker.support := fun w =>
      hJB (Scheme.IdealSheafData.range_subschemeι J ▸ Set.mem_range_self _)
    have : IsReduced W' := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support i (j ≫ J.subschemeι ≫ s₁) hg
    have hw' : h w' = genericPoint W := by
      apply i.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hh]
      simp [hz, hs₁]
    obtain ⟨U', hU'ne, hU'iso⟩ := GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem i h (j ≫ J.subschemeι) s₁ U hiso (by rw [hh]; simp)
      hU ⟨w', hw'⟩
    have hq : h ≫ p = j ≫ J.subschemeι ≫ s₁ ≫ f := by rw [← hif, reassoc_of% hh]
    have : Smooth (j ≫ J.subschemeι ≫ s₁ ≫ f) := by
      have := hsm; infer_instance
    have hpft : LocallyOfFiniteType p := by rw [← hif]; infer_instance
    have hd := GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' F W W' p (h ≫ p) h hpft (by rw [hq]; infer_instance) rfl U' hU'ne hU'iso
    refine ⟨W', h, U', hW', ?_, ?_, hU'ne, hU'iso⟩
    · rw [hq]; exact GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F W' _ n inferInstance (hd.trans hdim)
    · rw [hq, ← Category.assoc]
      exact isProjOver_comp_closed _ (isProjOver_seq f hseq₁ (ProjSpace.isProjOver_pspace_str F _))

end GlobalTheory.WeakRes
end
end
end
