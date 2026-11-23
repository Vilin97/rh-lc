module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVariety

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalOpen

theorem exists_mul_isInteger (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ f : A, f ≠ 0 ∧ ∀ y : K, IsIntegral A y → ∃ a : A, algebraMap A K a = f • y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A K => (z : K))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)),
      ∃ a : A, algebraMap A K a = (b : A) • (z : K) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add (f := _), ha, hc, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]
  exact key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)

theorem exists_isIntegrallyClosed_away (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing A
  obtain ⟨f, hf, h⟩ := exists_mul_isInteger A K
  refine ⟨f, hf, ?_⟩
  let B := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y) := fun y =>
    IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle
  letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra
  have : IsScalarTower A B K := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f)
    (Rₘ := B) x hx
  obtain ⟨a, ha⟩ := h _ hm
  let t : Submonoid.powers f := ⟨f, Submonoid.mem_powers f⟩ * m
  refine ⟨IsLocalization.mk' B a t, ?_⟩
  have e := congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at e
  refine (hg t).mul_right_cancel ?_
  rw [e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]
  rfl

theorem exists_normal_opens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  intro k _ X p D h
  have := h.isIntegral
  have := h.finite
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, hft, -⟩ := RegGenSmooth.chart_props h i hi
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance hft
  have := finite_integralClosure_of_essFiniteType_int A
  obtain ⟨f, hf, hc⟩ := exists_isIntegrallyClosed_away A
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hB : GlobalTheory.IsNormalScheme (Sp B) := GlobalTheory.IsNormalScheme.spec (.of B)
  have : GlobalTheory.IsNormalScheme j.opensRange.toScheme := .of_isIso j.isoOpensRange.hom
  refine ⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩
  exact ⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩

end GlobalTheory.NormalOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVarietyStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

theorem _root_.GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  first | exact @GlobalTheory.NormalOpen.exists_normal_opens | exact GlobalTheory.NormalOpen.exists_normal_opens | (intros; apply GlobalTheory.NormalOpen.exists_normal_opens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

end GlobalTheory.GraphClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem exists_normalisation_of_locallyClosed : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  intro O _ _ _ P U s Ω j hs _ hn hfl
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ Ω.ι)
  obtain ⟨h, eh⟩ : ∃ h : U ⟶ P, h = j ≫ Ω.ι := ⟨_, rfl⟩
  have : QuasiCompact h := eh ▸ inferInstance
  have : IsSeparated h := eh ▸ inferInstance
  have : LocallyOfFiniteType h := eh ▸ inferInstance
  have : Flat (h ≫ s) := by rw [eh, Category.assoc]; exact hfl
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h s
      fun x hx => charZero_residueField_of_flat (h ≫ s) hx
  have : Flat (h.toNormalization ≫ h.fromNormalization ≫ s) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
    infer_instance
  exact ⟨h.normalization, h.fromNormalization, h.toNormalization, inferInstance,
    IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization h _,
    isPullback_toNormalization_of_mono j Ω.ι h eh, h.toNormalization.denseRange⟩

end GlobalTheory.GraphClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpac

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormalModel

open TopologicalSpace

theorem exists_normal_model : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  intro K Ω _ _ _ _ D m y X _ p g ψ ⟨hgp, hX, hψ, hK, hy⟩
  obtain ⟨W, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety (𝓞 K) X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom (𝓞 K))) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom (𝓞 K)) = algebraMap ℤ (𝓞 K) := RingHom.ext_int _ _
      change (Int.castRingHom (𝓞 K)).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom (𝓞 K))) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X W.toScheme
      (p ≫ spMap (Int.castRingHom (𝓞 K))) W (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty W.toScheme := hne.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ W.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = W.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom (𝓞 K))) := by rwa [Category.assoc]
  have har : IsArithVar (ν ≫ p) D := ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq (𝓞 K) X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩

  have hη : ν (genericPoint Y) ⤳ genericPoint X := specializes_of_eq hgen
  have hWη : W.ι (genericPoint W.toScheme) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have heη : e (genericPoint W.toScheme) ⤳ genericPoint Y := specializes_of_eq hg
  have hbij : Function.Bijective (SmallSec.fnMap ν hη) := by
    refine ⟨(SmallSec.fnMap ν hη).injective, fun u => ?_⟩
    obtain ⟨t, ht⟩ := SmallSec.fnMap_surjective W.ι hWη (SmallSec.fnMap e heη u)
    refine ⟨t, (SmallSec.fnMap e heη).injective ?_⟩
    rw [← ht, ← ProjSpace.fnMap_comp e ν heη hη (ProjSpace.comp_genericPoint_specializes _ _ heη hη)]
    exact ProjSpace.fnMap_congr hfac _ _ t
  refine ⟨Y, ‹_›, ν ≫ p, ν ≫ g, (SmallSec.fnMap ν hη).comp ψ, by rw [Category.assoc, hgp], har, hnY,
    hbij.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · have e₁ : ν.app ⊤ (algX p ⊤ a) = algX (ν ≫ p) ⊤ a := by
      simp only [algX, RingHom.comp_apply]
      rw [← Scheme.Hom.appLE_comp_appLE ν p ⊤ ⊤ ⊤ (by simp) (by simp)]
      rw [Scheme.Hom.app_eq_appLE ν]
      rfl
    rw [RingHom.comp_apply, hK, SmallSec.fnMap_fnOf ν hη _ (Opens.mem_top _), e₁]
    rfl
  · have hX' : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := (pull_U _ g i).ge (by
      have h' : ν (genericPoint Y) ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      rw [hgen] at h'
      exact h')
    have key (a : Fin (m + 1)) : fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) (ν ≫ g)).f i) =
        SmallSec.fnMap ν hη (fnOf _ hX' ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) := by
      have h₁ : genericPoint Y ∈ (ν ≫ g) ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      have h₂ : genericPoint X ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ g i).le hX'
      change fnOf _ h (resG Y _ _) = SmallSec.fnMap ν hη (fnOf _ hX' (resG X _ _))
      rw [fnOf_resG, fnOf_resG, SmallSec.fnMap_fnOf ν hη h₂ h₁, Scheme.Hom.comp_app]
      rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, key, key, ← map_mul, ← map_mul, hy k l i hX']

end GlobalTheory.NormalModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpacStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo


theorem _root_.GlobalTheory.T.exists_normal_arithmeticVariety_model_projectiveSpace : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  first | exact @GlobalTheory.NormalModel.exists_normal_model | exact GlobalTheory.NormalModel.exists_normal_model | (intros; apply GlobalTheory.NormalModel.exists_normal_model <;> assumption)
end
end
