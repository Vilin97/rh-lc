module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVRStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSectionsStatement
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBaseStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObject

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem dense_asIdeal_eq_bot_spMap (n : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) : Dense {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
  let p₀ : Sp V₁ := ⟨⊥, Ideal.isPrime_bot⟩
  let K := FractionRing V₁
  have hinj : Function.Injective (algebraMap V₁ K) := IsFractionRing.injective V₁ K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hmem : p₀ ∈ {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
    let q : Sp K := ⟨⊥, Ideal.isPrime_bot⟩
    have h := GlobalTheory.AbChart.asIdeal_eq_bot_of_charZero n K (spMap ((algebraMap V₁ K).comp b₁)) q
    show Ideal.comap b₁ (⊥ : Ideal V₁) = ⊥
    have hc : Ideal.comap (algebraMap V₁ K) (⊥ : Ideal K) = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => hinj (by rw [ha, map_zero])
    rw [← hc, Ideal.comap_comap]
    exact h
  have hcl : closure ({p₀} : Set (Sp V₁)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact (PrimeSpectrum.le_iff_mem_closure (R := V₁) p₀ x).1 bot_le
  refine Dense.mono (Set.singleton_subset_iff.2 hmem) ?_
  exact dense_iff_closure_eq.2 hcl

theorem exists_sFam_point : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal →
    ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  intro n hn hodd h V₁ _ _ _ b₁ s hs
  obtain ⟨F⟩ : Nonempty (SFam h n (zetaAway n)) := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact ⟨zeroFam n hn⟩
    · exact GlobalTheory.SiegelTor.exists_sFam_cycAway h n hh hn hodd
  obtain ⟨x, hx, hpb⟩ := F.rep (Sp V₁) (spMap b₁) s inferInstance (dense_asIdeal_eq_bot_spMap n V₁ b₁) hs
  exact ⟨F, x, hx, hpb⟩

end GlobalTheory.LowChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObjectStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_siegel_family_point_of_principal_object : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁] (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal → ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  first | exact @GlobalTheory.LowChart.exists_sFam_point | exact GlobalTheory.LowChart.exists_sFam_point | (intros; apply GlobalTheory.LowChart.exists_sFam_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e

    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.grpPullback_divisionPoints_push_eq : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  first | exact @GlobalTheory.DivPush.push_div_pts | exact GlobalTheory.DivPush.push_div_pts | (intros; apply GlobalTheory.DivPush.push_div_pts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem exists_fibrePow_point_of_polAV : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  intro n hn hodd V _ _ _ hV hD b PB r c hc
  obtain ⟨V₁, _, _, _, f₁, s, β, β₂, d, h1, h2, h3, h4, h5, hP, hpb, hsq, hlb, hd⟩ :=
    GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR n hn hodd V hV hD b PB r c
  have : CharZero V₁ := h1.2.2.2
  obtain ⟨F, x, hx, hpbF⟩ := GlobalTheory.T.exists_siegel_family_point_of_principal_object n hn hodd PB.g V₁ (f₁.comp b) s hP
  obtain ⟨v, hs, β₁, β₁₂, p1, p2, p3, p4⟩ :=
    GlobalTheory.T.exists_siegelObject_fibrePower_at_sections F (spMap f₁) (spMap (f₁.comp b)) x hx s hpbF PB.A (abelian₂ PB.A PB.L) β β₂ hpb hsq hlb r d
  refine ⟨F, V₁, inferInstance, inferInstance, inferInstance, f₁, v, hs, h1, h2, h3, h4, h5, β₁, β₁₂, p1, p2, p3,
    fun a => ?_⟩
  rw [p4]
  exact GlobalTheory.T.grpPullback_divisionPoints_push_eq (spMap f₁) s.A PB.A β hpb n r d c hc hd a

end GlobalTheory.LowChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  first | exact @GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | exact GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | (intros; apply GlobalTheory.LowChart.exists_fibrePow_point_of_polAV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_lowBase_of_trait : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn ho V _ _ _ hV hd b PB r c hc
  obtain ⟨F, V₁, _, _, _, f₁, v, hs, hV₁, hd₁, hi₁, hf₁, hl₁, β₁, β₁₂, hp₁, hq₁, hL₁, hc₁⟩ :=
    GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr n hn ho V hV hd b PB r c hc
  obtain ⟨L, V', _, _, _, f, κ, e, hh, hV', hd', hi, hf, hl, hκ, hb, B', _, β', β'', β₂, β₂', hp, hp', hq, hq', hL, hx⟩ :=
    GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base n hn ho PB.g F r V₁ hV₁ hd₁ (f₁.comp b) v hs
  have es : spMap (f.comp f₁) = spMap f ≫ spMap f₁ := by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hl' : IsLocalHom (f.comp f₁) := RingHom.isLocalHom_comp f f₁
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f.comp f₁, κ, e, hh, hV', hd', hi.comp hi₁,
    hf.comp hf₁, hl', hκ, ?_, B', inferInstance, β' ≫ β₁, β'', β₂ ≫ β₁₂, β₂', ?_, hp', isSquare_comp hq hq₁, hq', ?_, ?_⟩
  · rw [hb, RingHom.comp_assoc]
  · rw [es]
    exact hp.comp hp₁
  · have h1 : LBIso ((LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ PB.A PB.L).pull (β₂ ≫ β₁₂)) :=
      lbIso_pull_comp hL₁ β₂ rfl
    exact LBIso.trans (pull_isLB (LB.isLB_linComb PB.isLB _ _) _) (pull_isLB (LowChart.siegAt F v _ hs).isLB _)
      (pull_isLB (LB.isLB_linComb L.T.M.isLB _ _) _) h1.symm hL
  · intro a
    obtain ⟨x, h1, h2, h3⟩ := hx a
    refine ⟨x, h1, ?_, h3⟩
    rw [← Category.assoc, h2, Category.assoc, hc₁, es, Category.assoc]

end GlobalTheory.TChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lower_base_of_trait_abelian_part : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.TChart.exists_lowBase_of_trait | exact GlobalTheory.TChart.exists_lowBase_of_trait | (intros; apply GlobalTheory.TChart.exists_lowBase_of_trait <;> assumption)
end
end
