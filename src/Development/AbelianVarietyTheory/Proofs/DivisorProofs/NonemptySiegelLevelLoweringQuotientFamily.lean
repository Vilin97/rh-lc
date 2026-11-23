module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteActionStatement
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isQProjOver_target_galoisCover_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGaloisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principal_siegel_lower_level_descends_galois : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  first | exact @GlobalTheory.PrincipalDescent.principal_descends | exact GlobalTheory.PrincipalDescent.principal_descends | (intros; apply GlobalTheory.PrincipalDescent.principal_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  first | exact @GlobalTheory.SiegAct.siegel_group_action | exact GlobalTheory.SiegAct.siegel_group_action | (intros; apply GlobalTheory.SiegAct.siegel_group_action <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescentEtaleCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmoothDescent

theorem smoothOfRelativeDimension_of_etale_cover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescentEtaleCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descent_etaleCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover_noetherian | exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover_noetherian | (intros; apply GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover_noetherian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem nonempty_sQuot : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N →
    j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  intro h n N F j hn hN hdvd hj hfin het
  have hn0 : n ≠ 0 := by omega
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ := GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive h n N F j hn hN hdvd hj
  have hjf : j.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have hq : IsQProjOver (F.s ≫ spMap j) :=
    (GlobalTheory.isQProjOver_baseChange_and_finite_restrict _ _ j F.X (F.s ≫ spMap j)).2 F.s hjf F.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction (cycAway n) F.X (F.s ≫ spMap j) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_galoisCover_noetherian (cycAway n) F.X Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ sY) := by
    rw [hπ]
    haveI := F.smooth
    haveI : SmoothOfRelativeDimension 0 (spMap j) := inferInstance
    have := smoothOfRelativeDimension_comp (h * (h + 1) / 2) 0 F.s (spMap j)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension (h * (h + 1) / 2) sY :=
    GlobalTheory.T.smoothOfRelativeDimension_descent_etaleCover (cycAway n) F.X Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨c, hc, hlowc⟩ := GlobalTheory.T.principal_siegel_lower_level_descends_galois h n N (cycAway n) (cycAway N) (cycBase hn0) (zetaAway N) j F.X Y F.s π sY F.univ
    Ga ρ ν hN0 (isUnit_natCast hN0) hdvd (by rw [cycBase_ζ]; exact hj) hπ hG (by rw [hπ]; exact hq) hft F.princ hν1
    hνmul hlow
  refine ⟨⟨Y, sY, hsY, hqY, c, hc, π, hπ, hG.fin, hG.etale, hG.onto, hlowc, ?_⟩⟩
  intro R _ _ y y' s' c' h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans R y y' s' c' h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory.SiegLev

end
end
end
