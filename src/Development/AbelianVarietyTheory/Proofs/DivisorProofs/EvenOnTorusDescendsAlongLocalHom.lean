module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapClosedFibreLocalHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapOfLineBundleIsoRescaledStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubTriv
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorusCubTriv

open GlobalTheory GlobalTheory.UU GlobalTheory.EvenGenTorus TorusCube

theorem exists_cubTriv : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  intro k _ hk G₀ _ _ X _ _ _ P₀ i hi
  letI := hk.toField
  haveI := hi
  haveI : IsAffine (splitTorus (Sp k) X).left := isAffine_of_isAffineHom (splitTorus (Sp k) X).hom
  haveI := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus k X
  obtain ⟨τ, hτ⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb P₀.L.isLB (K := PUnit) (fun _ => i.left) (fun _ => 1))
  have e1 : (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left ≫ i.left = (1 : splitTorus (Sp k) X ⟶ G₀).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i.left) (fun _ => 1) τ
      (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp k)) (x : T ⟶ splitTorus (Sp k) X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val τ x.left z J * (val τ (1 : T ⟶ splitTorus (Sp k) X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩⟩
  have a := cube k X G₀ i P₀.L P₀.c τ hτ T x y u z J hJ
  simp only [v T _ z J hJ]
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

end GlobalTheory.Mum.TorusCubTriv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  first | exact @GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | exact GlobalTheory.Mum.TorusCubTriv.exists_cubTriv | (intros; apply GlobalTheory.Mum.TorusCubTriv.exists_cubTriv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivialisationCompMonHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.CubTrivComp

theorem val_cast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (h ▸ t : LB.Gen (LB.LinComb L φ' ε)) r z J = val t r z J := by
  subst h; rfl

theorem isGen_cast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (h ▸ t : LB.Gen (LB.LinComb L φ' ε)).IsGen := by
  subst h; exact ht

theorem exists_even_comp : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H']
    (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i,
    GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  intro S G H H' _ _ _ _ P i e he σ hσ
  have hφ : (fun k => e.left ≫ (![i.left, (1 : H' ⟶ G).left] : Fin 2 → (H'.left ⟶ G.left)) k) =
      ![(e ≫ i).left, (1 : H ⟶ G).left] := by
    funext k
    fin_cases k
    · exact (Over.comp_left _ _ _ e i).symm
    · show e.left ≫ (1 : H' ⟶ G).left = (1 : H ⟶ G).left
      rw [← Over.comp_left, MonObj.comp_one]
  let s₁ : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![(e ≫ i).left, (1 : H ⟶ G).left] ![1, -1]) :=
    hφ ▸ LB.pullGen P.L.L _ _ σ.s e.left
  have v : ∀ {T : Over S} (x : T ⟶ H) {z : T.left} {J}, Good P.L.L z J →
      val s₁ x.left z J = val σ.s (x ≫ e).left z J := fun x z J hJ =>
    (val_cast hφ _ _ _ _).trans ((val_pull hJ σ.s e.left x.left).trans (by rw [Over.comp_left]))
  refine ⟨⟨s₁, isGen_cast hφ (DVR.pullGen_isGen _ _ _ _ σ.gen _), fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · have c := σ.cub T (x ≫ e) (y ≫ e) (u ≫ e) z J hJ
    simp only [← MonObj.mul_comp, Category.assoc] at c
    simp only [v _ hJ]
    exact c
  · show val s₁ (x⁻¹).left z J = val P.sym (x ≫ e ≫ i).left z J * val s₁ x.left z J
    rw [v _ hJ, v _ hJ, GrpObj.inv_comp, hσ T (x ≫ e) z J hJ, Category.assoc]

end GlobalTheory.CubTrivComp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivialisationCompMonHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H'] (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i, GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  first | exact @GlobalTheory.CubTrivComp.exists_even_comp | exact GlobalTheory.CubTrivComp.exists_even_comp | (intros; apply GlobalTheory.CubTrivComp.exists_even_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusFactorBaseChangeField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isMonHom_of_comp_mono_torus {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N P : C}
    [MonObj M] [MonObj N] [MonObj P] (e : M ⟶ N) (i : N ⟶ P) [Mono i] [IsMonHom i] [IsMonHom (e ≫ i)] :
    IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom,
      ← Category.assoc, ← tensorHom_comp_tensorHom]

theorem exists_torus_factor : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  intro k k' _ _ hk' ρ G₀ _ G'₀ _ β₀ hβ₀ X X' _ _ _ _ Q₀ Q'₀
  letI : Field k' := hk'.toField
  obtain ⟨i₁, h₁, -⟩ := GlobalTheory.UU.existsUnique_torusCompat hβ₀.1 Q₀.i
  haveI := Q₀.i_hom
  haveI := Q'₀.i_hom
  haveI := Q'₀.q_hom
  haveI hi₁ : IsMonHom i₁ := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ h₁
  haveI : IsProper Q'₀.B.hom := Q'₀.isAb.proper
  have hc : i₁ ≫ Q'₀.q = toUnit _ ≫ η[Q'₀.B] := by
    have h := GlobalTheory.TorusConst.eq_const (K := k') X (i₁ ≫ Q'₀.q)
    rw [IsMonHom.one_hom] at h
    exact h
  let e := Q'₀.isKernel.lift i₁ (toUnit _) hc
  have he : e ≫ Q'₀.i = i₁ := Q'₀.isKernel.lift_fst _ _ hc
  haveI : Mono Q'₀.i := by
    haveI : Mono (η[Q'₀.B]) := ⟨fun a b _ => toUnit_unique a b⟩
    exact Q'₀.isKernel.mono_fst_of_mono
  haveI : IsMonHom (e ≫ Q'₀.i) := he ▸ hi₁
  exact ⟨i₁, e, isMonHom_of_comp_mono_torus e Q'₀.i, he, h₁⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusFactorBaseChangeFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torus_factor_baseChange_field : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  first | exact @GlobalTheory.Mum.exists_torus_factor | exact GlobalTheory.Mum.exists_torus_factor | (intros; apply GlobalTheory.Mum.exists_torus_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | exact GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | (intros; apply GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem evenOn_of_local : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) β → IsProper (pullback.snd G'.hom (jK W)) → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'), LBIso P'.L.L (P.L.L.pull β) → EvenOn P' → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ hG G' _ _ β hβ hp P P' hL hE X _ _ _ ⟨Q₀⟩
  have hG' := GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor _ _ _ G G' β hβ hG
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic G' hG' hp
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cubicalStructureMap_of_lineBundleIso_rescaled _ _ _ G G' β hβ.1.w (GlobalTheory.UU.TowerEx.toBase_mul hβ hβ.1.w) h3 P P' hL
  obtain ⟨X', _, _, _, Q'₀, P'₀, hlev', σ', hσ'⟩ := hE
  obtain ⟨P₀, hlev⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  obtain ⟨ρ, β₀, hβ₀, w₀, hw₀⟩ := GlobalTheory.T.exists_cubicalStructureMap_closedFibre_localHom R W φ hφ G G' β hβ P P' w hw P₀ P'₀ hlev hlev'
  have hk : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal R)
  have hk' : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact IsLocalRing.maximalIdeal.isMaximal W)
  obtain ⟨i₁, e, he, rfl, hc⟩ := GlobalTheory.T.exists_torus_factor_baseChange_field _ _ hk' ρ _ _ β₀ hβ₀ X X' Q₀ Q'₀
  obtain ⟨σ₁, hσ₁⟩ := GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom _ _ _ _ P'₀ Q'₀.i e he σ' hσ'
  have := Q₀.i_hom
  have hi₁ : IsMonHom (e ≫ Q'₀.i) := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ hc
  obtain ⟨σ⟩ := @GlobalTheory.T.exists_cubicalTrivialisation_splitTorus_field _ _ hk _ _ _ X _ _ _ P₀ Q₀.i Q₀.i_hom
  obtain ⟨χ, hχ⟩ := @GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt _ _ _ _ hk hk' ρ _ _ _ _ _ _ β₀ hβ₀ P₀ P'₀ w₀ hw₀ X _ _ _ Q₀.i (e ≫ Q'₀.i) Q₀.i_hom hi₁ hc σ σ₁ hσ₁
  exact ⟨X, inferInstance, inferInstance, inferInstance, Q₀, P₀, hlev, _, hχ⟩

end GlobalTheory.Mum
end
end
