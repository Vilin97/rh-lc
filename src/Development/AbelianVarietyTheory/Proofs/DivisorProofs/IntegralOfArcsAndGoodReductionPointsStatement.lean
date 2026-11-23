module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerX
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingLocalizationPowerSeriesUnStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Mathlib.RingTheory.Localization.Cardinality

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerXStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  first | exact @GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | exact GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | (intros; apply GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcIntegral

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem ev_factor {Z : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z₁ : Sp A ⟶ Z) (z₂ : Sp B ⟶ Z)
    (e : z₂ = spMap φ ≫ z₁) (W : Z.Opens) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W) (f : Γ(Z, W)) :
    ev z₂ W h₂ f = φ (ev z₁ W h₁ f) := by
  subst e
  rw [GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]
  rfl

theorem point_cases (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Sp R) :
    (∃ p : Sp K, spMap (algebraMap R K) p = x) ∨ x = IsLocalRing.closedPoint R := by
  by_cases h : x.asIdeal = ⊥
  · refine Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · refine Or.inr (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)

theorem spMap_closedPoint {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  IsLocalRing.comap_closedPoint f

theorem spMap_closedPoint_of_surjective {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))

theorem mk_le_continuum_of_finite {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Finite)
    (hA : Cardinal.mk A ≤ Cardinal.continuum) : Cardinal.mk B ≤ Cardinal.continuum := by
  letI := g.toAlgebra
  haveI : Module.Finite A B := hg
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]
  exact (pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)

theorem mem_range_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K)
    (hx : la x ∈ (algebraMap A B).range) : x ∈ (algebraMap R K).range := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨t, ht⟩ := hx
  have h1 : algebraMap A B (e r * t) = 1 := by
    rw [map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]
  have h2 : e r * t = 1 := IsFractionRing.injective A B (h1.trans (map_one _).symm)
  have hu : IsUnit r := isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  have h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1 := by
    rw [← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]
  exact (mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem range_j_subset {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  rw [Model.j, Scheme.Hom.comp_apply]
  exact h

theorem exists_frac_lift {A K L : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (f : A →+* L) (hf : Function.Injective f) : ∃ fK : K →+* L, fK.comp (algebraMap A K) = f :=
  ⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩

theorem exists_away_lift {A S L : Type} [CommRing A] [CommRing S] [Algebra A S] (x : A) [IsLocalization.Away x S]
    [CommRing L] (f : A →+* L) (hf : IsUnit (f x)) : ∃ F : S →+* L, ∀ a, F (algebraMap A S a) = f a :=
  ⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩

theorem isUnit_map_X {A : Type} [CommRing A] (κ : A →+* ℂ) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ) PowerSeries.X) := by
  rw [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)

end GlobalTheory.ArcIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPoints

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open GlobalTheory.ArcIntegral

namespace GlobalTheory.ArcIntegralMixed

theorem exists_denominator {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] (ϖ : A)
    (hϖ : Irreducible ϖ) (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (v : S)
    (hv : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (ρ : PowerSeries A →+* R) (ψ : S →+* K),
      ψ.comp (algebraMap (PowerSeries A) S) = (algebraMap R K).comp ρ → IsUnit (ρ PowerSeries.X) →
      ψ v ∈ (algebraMap R K).range) :
    ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s := by
  obtain ⟨hp, hdvr⟩ := GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser A ϖ hϖ
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra (PowerSeries A) R), IsLocalization.AtPrime R (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}) :=
    ⟨_, _, _, hdvr, _, inferInstance⟩
  let K := FractionRing R
  have hρ : Function.Injective (algebraMap (PowerSeries A) R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}))
  let f : PowerSeries A →+* K := (algebraMap R K).comp (algebraMap (PowerSeries A) R)
  have hf : Function.Injective f := (IsFractionRing.injective R K).comp hρ
  have hC : Function.Injective (f.comp (PowerSeries.C (R := A))) := hf.comp PowerSeries.C_injective
  haveI : CharZero K := (RingHom.charZero_iff hC).1 inferInstance
  have h0 : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero
  have hu : IsUnit (f (PowerSeries.C ϖ * PowerSeries.X)) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hf).2 h0)
  obtain ⟨ψ, hψ⟩ := exists_away_lift (S := S) _ f hu
  have hψi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, ha⟩ :=
      IsLocalization.surj (Submonoid.powers (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A)) x
    have ha0 : a = 0 := hf (by
      have := congrArg ψ ha
      rw [map_mul, hx, zero_mul, hψ] at this
      rw [← this, map_zero])
    rw [ha0, map_zero] at ha
    exact (IsLocalization.map_units S m).mul_left_eq_zero.1 ha
  have hX : (PowerSeries.X : PowerSeries A) ∈ (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl := by
    intro hm
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
    have := congrArg (PowerSeries.coeff 1) hq
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul] at this
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ this.symm)
  obtain ⟨r, hr⟩ := hv R K (algebraMap _ R) ψ (RingHom.ext hψ) (IsLocalization.map_units R ⟨_, hX⟩)
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl r
  refine ⟨s, t, fun hd => t.2 (Ideal.mem_span_singleton.2 hd), hψi ?_⟩
  rw [map_mul, hψ, hψ, ← hr]
  exact (map_mul (algebraMap R K) _ _).symm.trans (congrArg (algebraMap R K) hst)

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem integral_of_arcs_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  intro E _ _ _ H Dw l Xo c V Y h3 h4 hS hj U₀ W₀ f₀ hUW harc hgood R K _ _ _ _ _ _ _ z y hcount hU hy h
  by_cases hab : Set.range z ⊆ abLocus Y.t.G
  · exact hgood R K z y hU hy hab h
  have hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ Y.X), Set.range w ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ →
      ⊤ ≤ w ⁻¹ᵁ W₀ := fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, rfl⟩)
  obtain ⟨io, hio⟩ := exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨b₀, hover⟩ := exists_spMap (z ≫ Y.s)
  have hcomp : (algebraMap R K).comp b₀ = io.comp V.subtype := spMap_injective (by
    rw [← sp_comp, ← sp_comp, ← hover, ← hio, ← Category.assoc, ← hy, Model.j, ← Y.jQ_over]
    simp only [Category.assoc, pullback.condition])
  have hgen : Set.range (spMap (algebraMap R K) ≫ z) ⊆ Set.range Y.j := by
    rw [← hy]; rintro _ ⟨x, rfl⟩; exact ⟨y x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hch : CharZero R := (RingHom.charZero_iff (IsFractionRing.injective R K)).2 inferInstance
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum R hcount
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  obtain ⟨iK, hiK⟩ := exists_frac_lift (K := K) _ hiF
  let y' : Sp T.V ⟶ Y.X := spMap i ≫ z
  let b : V →+* T.V := i.comp b₀
  let io' : c.F →+* T.Fr := iK.comp io
  have hbio : (algebraMap T.V T.Fr).comp b = io'.comp V.subtype := by
    simp only [b, io']
    rw [← RingHom.comp_assoc, ← hiK, RingHom.comp_assoc, hcomp, RingHom.comp_assoc]
  have hy' : y' ≫ Y.s = spMap b := by
    simp only [y', Category.assoc]; rw [hover, sp_comp]
  let zT : Sp T.Fr ⟶ Xo.XF c := spMap iK ≫ y
  have hzT : zT ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' := by
    simp only [y', zT]
    rw [Category.assoc, hy, ← Category.assoc, sp_comp, hiK, ← sp_comp, Category.assoc]
  have hzT' : zT ≫ pullback.snd _ _ = spMap io' := by
    simp only [zT, io']
    rw [Category.assoc, hio, sp_comp]
  clear_value zT
  have hbad : ¬ Set.range y' ⊆ abLocus Y.t.G := fun hy => hab (by
    rintro _ ⟨x, rfl⟩
    rcases point_cases R K x with ⟨p, rfl⟩ | rfl
    · exact range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)
    · have e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R := spMap_closedPoint i
      have := hy ⟨IsLocalRing.closedPoint T.V, rfl⟩
      change (spMap i ≫ z) (IsLocalRing.closedPoint T.V) ∈ _ at this
      erw [Scheme.Hom.comp_apply, e] at this; exact this)
  obtain ⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c V Y h3 hS T io' b y' zT hbio hy' hzT' hzT hbad
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V := hϖ.maximalIdeal_eq ▸ T'.cpl
  obtain ⟨χ₀, hχ, hsp⟩ := h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover₀, hab₀, hopen, hW⟩ := (hχ χ₀).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ₀).1 hW
  obtain ⟨-, -, evu, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl
  have hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hg
  obtain ⟨gF, hgF'⟩ := exists_frac_lift (K := T.Fr) _ hgF
  have hχy : spMap evu ≫ χ₀ = spMap g ≫ y' := hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      have e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j := by
        rw [hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]
        rfl
      exact ⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX
  have hχz : spMap evu ≫ χ₀ = spMap g ≫ spMap i ≫ z := hχy
  haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg
  have hχU : ⊤ ≤ χ₀ ⁻¹ᵁ U₀ := by
    have hc : χ₀ (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀ := by
      rw [← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]
      change (spMap evu ≫ χ₀) (IsLocalRing.closedPoint T'.V) ∈ U₀
      rw [hχz]
      exact hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))
    exact ((IsLocalRing.closed_point_mem_iff (U := χ₀ ⁻¹ᵁ U₀)).1 hc).ge

  let S := Localization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries T'.V)
  let ι : PowerSeries T'.V →+* S := algebraMap _ _
  have huX : IsUnit (ι (PowerSeries.C ϖ * PowerSeries.X)) := IsLocalization.Away.algebraMap_isUnit _
  have hSj : Set.range (spMap ι ≫ χ₀) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    exact hopen (spMap ι x) fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ι (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal from hx) huX)
  have hSW : ⊤ ≤ (spMap ι ≫ χ₀) ⁻¹ᵁ W₀ := hzW _ hSj (le_preimage_comp _ hχU)

  have hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum := by
    rw [show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact mk_le_continuum_of_finite g hgf hcard
  obtain ⟨κ, hκ⟩ := @GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _
    (gF.comp io').toAlgebra hcard' c.F.val.toRingHom
  let κ₀ : T'.V →+* ℂ := κ.comp (algebraMap T'.V T'.Fr)
  have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b) := by
    rw [← hκ]
    change κ.comp (gF.comp (io'.comp V.subtype)) = κ.comp (((algebraMap T'.V T'.Fr).comp g).comp b)
    rw [← hbio, ← hgF']; rfl
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ
    (g.comp b) a κ₀ hκ₀ _ hb'
  obtain ⟨hW₁, -⟩ := hbc a₁ p hp
  obtain ⟨W₁, -⟩ := hW₁ χ₀ W
  have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
  have hXu : IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ (isUnit_map_X κ₀)
    rw [RingHom.comp_apply, PowerSeries.map_C]
    exact ((IsUnit.mk0 _ hϖ0).map _).map _
  obtain ⟨ιC, hιC'⟩ := exists_away_lift (S := S) _ _ hXu
  have hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s) :=
    fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)
  have hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ = spMap ιC ≫ spMap ι ≫ χ₀ := by
    rw [← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp,
      show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]
  have hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀) ⁻¹ᵁ W₀ := by
    rw [hpt]; exact le_preimage_comp _ hSW
  have hres := harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀) ((Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by
      rw [Category.assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by
      refine hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))
    (le_preimage_comp _ hχU) hLh
  rw [ev_factor ιC (spMap ι ≫ χ₀) _ hpt W₀ hSW hLh f₀] at hres

  have hden := exists_denominator ϖ hϖ S (ev (spMap ι ≫ χ₀) W₀ hSW f₀) (by
    intro R' K' _ _ _ _ _ _ _ ρ ψ hψ hρ
    have e : spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀ = spMap ψ ≫ spMap ι ≫ χ₀ := by
      rw [← Category.assoc, ← Category.assoc (spMap ψ), sp_comp, sp_comp, ← hψ]
    have hW' : ⊤ ≤ (spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀) ⁻¹ᵁ W₀ := by
      rw [e]; exact le_preimage_comp _ hSW
    rw [← ev_factor ψ (spMap ι ≫ χ₀) _ e W₀ hSW hW' f₀]
    refine hgood R' K' (spMap ρ ≫ χ₀) (spMap ψ ≫ IsOpenImmersion.lift Y.j (spMap ι ≫ χ₀) hSj)
      (le_preimage_comp _ hχU) (by rw [Category.assoc, IsOpenImmersion.lift_fac, e]) ?_ hW'
    rintro _ ⟨x, rfl⟩
    exact (hab₀ (spMap ρ x)).2 fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ρ PowerSeries.X ∈ x.asIdeal from hx) hρ))
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X T'.V ϖ hϖ κ₀ hκ₀ S ιC hιC _ hres hden

  have hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [RingHom.comp_apply, map_mul evu, hevC, hevX]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2
      (mul_ne_zero hϖ.ne_zero hϖ.ne_zero))
  obtain ⟨φS, hφS⟩ := exists_away_lift (S := S) _ _ hϖu
  have hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i)) :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)
  obtain ⟨la, hla⟩ := exists_frac_lift (K := K) _ hgi
  have hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ := by
    have e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, hla]
    have e2 : spMap φS ≫ spMap ι ≫ χ₀ = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS,
        ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    rw [e1, e2]
  have hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s) := by
    rw [← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h),
      GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]
    rfl
  haveI : IsLocalHom (g.comp i) := inferInstance
  exact mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩

end GlobalTheory.ArcIntegralMixed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.integral_of_arcs_and_goodReduction_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  first | exact @GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good | exact GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good | (intros; apply GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good <;> assumption)
end
end
