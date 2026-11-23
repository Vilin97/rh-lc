module

public import Mathlib.AlgebraicGeometry.FunctionField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSectionOfPow

section

@[expose] public section

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechRoot

theorem gen_res {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE h).op).hom s) = (X.germToFunctionField V).hom s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

theorem nonempty_inf {X : Scheme.{0}} [IsIntegral X] (V W : X.Opens) [hV : Nonempty V] [hW : Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

theorem exists_section_of_pow {X : Scheme.{0}} [IsIntegral X] (hN : ∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b))
    {l : ℕ} (hl : 0 < l) (V : X.Opens) [Nonempty V] (f : Γ(X, V)) (t : X.functionField)
    (ht : t ^ l = (X.germToFunctionField V).hom f) : ∃ s : Γ(X, V), (X.germToFunctionField V).hom s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  refine exists_germToFunctionField_eq_of_mem_range_stalk ?_ hx
  haveI := hN x
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hl ?_)
  rw [ht, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx f]
  exact isIntegral_algebraMap

theorem charP_functionField {X : Scheme.{0}} [IsIntegral X] (l : ℕ) [Fact l.Prime] (h : (l : Γ(X, ⊤)) = 0) :
    CharP X.functionField l := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← map_natCast (X.germToFunctionField ⊤).hom, h, map_zero]

theorem exists_root : ∀ (X : Scheme.{0}) [IsIntegral X], (∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b)) → ∀ (l : ℕ) [Fact l.Prime], (l : Γ(X, ⊤)) = 0 → ∀ (J : Type) (U : J → X.Opens) (f : ∀ j, Γ(X, U j)) (n : ∀ j j', Γ(X, U j ⊓ U j')), (∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (f j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (f j') = n j j' ^ l) → ∀ (i : J) (b : X) (hb : b ∈ U i) (h : FractionRing (X.presheaf.stalk b)), h ^ l = algebraMap (X.presheaf.stalk b) _ ((X.presheaf.germ (U i) b hb).hom (f i)) → ∃ H : ∀ j, Γ(X, U j), ∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (H j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (H j') = n j j' := by
  intro X _ hN l _ hl J U f n hf i b hb h hh
  haveI := charP_functionField l hl
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  haveI : Nonempty (U i) := ⟨⟨b, hb⟩⟩
  let e := FractionRing.algEquiv (X.presheaf.stalk b) X.functionField
  have he : e h ^ l = (X.germToFunctionField (U i)).hom (f i) := by
    rw [← map_pow, hh, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hb (f i)
  have hg : ∀ j j' [Nonempty (U j)] [Nonempty (U j')] [Nonempty (U j ⊓ U j' : X.Opens)],
      (X.germToFunctionField (U j)).hom (f j) - (X.germToFunctionField (U j')).hom (f j') =
        (X.germToFunctionField (U j ⊓ U j')).hom (n j j') ^ l := by
    intro j j' _ _ _
    rw [← map_pow, ← hf, map_sub, gen_res, gen_res]
  have ex : ∀ j, ∃ H : Γ(X, U j), ∀ [Nonempty (U j)],
      (X.germToFunctionField (U j)).hom H ^ l = (X.germToFunctionField (U j)).hom (f j) := by
    intro j
    by_cases hj : Nonempty (U j)
    · haveI := nonempty_inf (U j) (U i)
      have ht : (e h + (X.germToFunctionField (U j ⊓ U i)).hom (n j i)) ^ l =
          (X.germToFunctionField (U j)).hom (f j) := by
        rw [add_pow_char, he, ← hg, add_sub_cancel]
      obtain ⟨s, hs⟩ := exists_section_of_pow hN hl0 (U j) (f j) _ ht
      exact ⟨s, by intro _; rw [hs, ht]⟩
    · exact ⟨0, by intro h; exact absurd h hj⟩
  choose H hH using ex
  refine ⟨H, fun j j' => ?_⟩
  by_cases hj : Nonempty (U j ⊓ U j' : X.Opens)
  · obtain ⟨⟨z, hz⟩⟩ := id hj
    haveI : Nonempty (U j) := ⟨⟨z, hz.1⟩⟩
    haveI : Nonempty (U j') := ⟨⟨z, hz.2⟩⟩
    apply X.germToFunctionField_injective (U j ⊓ U j')
    apply frobenius_inj X.functionField l
    change (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l = (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l
    rw [map_sub, gen_res, gen_res, sub_pow_char, hH, hH, hg]
  · exact fn_ext (V := U j ⊓ U j') fun x hx => absurd ⟨⟨x, hx⟩⟩ hj

end GlobalTheory.CechRoot
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRootStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.artin_schreier_cocycle_root : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary | exact GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary | (intros; apply GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary <;> assumption)
end
end
