module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperIffOfSplit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitChartForm

theorem jK_apply_eq_bot (R : Type) [CommRing R] [IsDomain R] (p : Sp (FractionRing R)) :
    (jK R) p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal = ⊥
  rw [@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.TraitChartForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiUnitOnOfNeUniv

section

@[expose] public section

noncomputable section

namespace GlobalTheory.DvrDataCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Ext

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Ext

section Move

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem psiUnitOn_of_ne_univ (D : DegPre R) (χ : D.X) {U : Set (Sp R)} (hU : U ≠ Set.univ) : PsiUnitOn D χ U := by
  intro j V _ hVU _ h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} e => ⟨1, by rw [IsFractionRing.injective R _ e]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (pow_ne_zero n hϖ.ne_zero))
    · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Rˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have e₁ : ϖ ^ n = (b : R) * (u⁻¹ : Rˣ) := by rw [hu, _root_.mul_right_comm, Units.mul_inv, _root_.one_mul]
      show z * algebraMap R _ (ϖ ^ n) = algebraMap R _ (a * (u⁻¹ : Rˣ))
      rw [e₁, map_mul, map_mul, ← _root_.mul_assoc]
      exact congrArg (· * _) e
  have : IsOpenImmersion (jK R) := IsOpenImmersion.of_isLocalization ϖ
  have hV : V ≤ (jK R).opensRange := by
    intro x hx
    have hx' : x ≠ closedPoint R := fun e => hU (Set.eq_univ_of_univ_subset (by
      have : V = ⊤ := (closedPoint_mem_iff V).1 (e ▸ hx)
      rw [this] at hVU
      exact hVU))
    have hb : x.asIdeal = ⊥ := by
      by_contra hb
      have := x.isPrime
      exact hx' (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hb)))
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    rw [hb]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  have := (jK R).isIso_app V hV
  have hb := ConcreteCategory.bijective_of_isIso ((jK R).app V)
  obtain ⟨r, hr⟩ := hb.2 (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
  refine ⟨r, ?_, hr⟩
  have hu : IsUnit (((jK R).app V).hom r) := by
    have : ((jK R).app V).hom r = _ := hr
    rw [this]
    exact (Units.isUnit _).map _
  exact (MulEquiv.isUnit_map (RingEquiv.ofBijective ((jK R).app V).hom hb)).1 hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

end GlobalTheory.DvrDataCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
end
end
end
