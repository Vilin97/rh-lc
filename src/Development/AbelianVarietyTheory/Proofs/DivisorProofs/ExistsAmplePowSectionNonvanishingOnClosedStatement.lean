module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionLineBundlePowFiniteIntStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetFiniteFibresIsAffineFiniteInt

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem ringChar_residueField_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    ringChar (X.residueField x) = ringChar (Y.residueField (f x)) := by
  haveI := (RingHom.charP_iff_charP (f.residueFieldMap x).hom (ringChar (Y.residueField (f x)))).1
    (ringChar.charP _)
  exact ringChar.eq _ _

theorem closeds_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) →
    IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  intro k _ X _ p D hX T hT
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  have hr : Set.range I.subschemeι = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  set q := I.subschemeι ≫ p ≫ spMap (Int.castRingHom k) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : LocallyQuasiFinite q := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    have hfin := hT (ringChar ((Sp ℤ).residueField y))
    refine Set.Finite.of_finite_image (f := I.subschemeι) (hfin.subset ?_)
      (I.subschemeι.isClosedEmbedding.injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hr.le ⟨z, rfl⟩, ?_⟩
    show ringChar _ = _
    rw [ringChar_residueField_eq (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z)]
    have e : (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z) = y := by
      rw [← hz, hq]; rfl
    rw [e]
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  have hA : IsAffine I.subscheme := isAffine_of_isAffineHom q
  refine ⟨hA, ?_⟩
  have hf : (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).Finite :=
    q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2)
  rw [RingHom.ext_int (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)
    (algebraMap ℤ Γ(I.subscheme, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetFiniteFibresIsAffineFiniteIntStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) → IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧ Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  first | exact @GlobalTheory.HSAmp.closeds_finite_int | exact GlobalTheory.HSAmp.closeds_finite_int | (intros; apply GlobalTheory.HSAmp.closeds_finite_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosed

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  intro k _ X _ p D hX P hA T hT hfin
  let Z : Closeds X := ⟨T, hT⟩
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int k X p D hX Z hfin
  haveI := hAff
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int _ hFin (P.L.B.pull i) (LB.isLB_pull hA.isLB i)
  obtain ⟨N, u, hN, hu⟩ := GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed k X p D hX P.L.B hA _ i n s hn hs
  obtain ⟨f, hf, hfu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P N).1 u
  refine ⟨N, hN, f, hf, ?_⟩
  rw [hfu]
  intro x hx
  apply hu
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | exact GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | (intros; apply GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed <;> assumption)
end
end
