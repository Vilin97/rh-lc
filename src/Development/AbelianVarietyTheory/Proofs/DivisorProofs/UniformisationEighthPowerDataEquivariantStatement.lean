module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowModel

variable {C : Type*} [Category C] {J : Type*}

theorem isIso_of_prod {X Y Z : C} {p : J → (X ⟶ Z)} {r : J → (Y ⟶ Z)}
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a)
    (hY : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ Y, ∀ a, x ≫ r a = y a)
    (f : X ⟶ Y) (hf : ∀ a, f ≫ r a = p a) : IsIso f := by
  obtain ⟨g, hg, -⟩ := hX Y r
  refine ⟨g, ?_, ?_⟩
  · exact (hX X p).unique (fun a => by rw [Category.assoc, hg, hf]) (fun a => Category.id_comp _)
  · exact (hY Y r).unique (fun a => by rw [Category.assoc, hf, hg]) (fun a => Category.id_comp _)

theorem prod_precomp {X X' Z : C} {p : J → (X ⟶ Z)} (e : X' ≅ X)
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X', ∀ a, x ≫ (e.hom ≫ p a) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T y
  refine ⟨x ≫ e.inv, fun a => by rw [Category.assoc, Iso.inv_hom_id_assoc, hx], fun x' hx' => ?_⟩
  rw [← hu (x' ≫ e.hom) (fun a => by rw [Category.assoc, hx']), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem prod_postcomp {X Z Z' : C} {p : J → (X ⟶ Z)} (e : Z ≅ Z')
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z')), ∃! x : T ⟶ X, ∀ a, x ≫ (p a ≫ e.hom) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T (fun a => y a ≫ e.inv)
  refine ⟨x, fun a => by rw [← Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id],
    fun x' hx' => hu x' (fun a => by rw [← hx' a, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])⟩

theorem prod_of_isLimit {X Z : C} {p : J → (X ⟶ Z)} (h : IsLimit (Fan.mk X p)) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a := fun T y =>
  ⟨Fan.IsLimit.lift h y, fun a => Fan.IsLimit.fac h y a, fun x hx =>
    Fan.IsLimit.hom_ext h _ _ fun a => by
      change x ≫ p a = Fan.IsLimit.lift h y ≫ p a
      rw [hx a]; exact (Fan.IsLimit.fac h y a).symm⟩

theorem prod_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) {X Z : Over S} {p : J → (X ⟶ Z)}
    (hX : ∀ (T : Over S) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : Over S') (y : J → (T ⟶ (Over.pullback j).obj Z)),
      ∃! x : T ⟶ (Over.pullback j).obj X, ∀ a, x ≫ (Over.pullback j).map (p a) = y a := by
  intro T y
  let adj := Over.mapPullbackAdj j
  obtain ⟨x, hx, hu⟩ := hX _ (fun a => (adj.homEquiv _ _).symm (y a))
  refine ⟨adj.homEquiv _ _ x, fun a => ?_, fun x' hx' => ?_⟩
  · rw [← adj.homEquiv_naturality_right, hx, Equiv.apply_symm_apply]
  · rw [← hu ((adj.homEquiv _ _).symm x') (fun a => by rw [← adj.homEquiv_naturality_right_symm, hx']),
      Equiv.apply_symm_apply]

end GlobalTheory.Poinc.Sep.PowModel


open GlobalTheory.Poinc.Sep.PowModel in
theorem GlobalTheory.Poinc.Sep.unif_pow_isPow_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hsa hα P c φc hφc pr hpr hP G _ _ hG D U
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  obtain ⟨κ, hκ, hκα⟩ := grpPullback_iso hφc hα
  haveI := U.gen_hom
  haveI := U₀.gen_hom
  have hf : ∀ u, IsMonHom (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv) := fun u => by
    haveI := hpr u
    infer_instance
  have hext : ∀ u, ∃ F : G ⟶ G₀, IsMonHom F ∧
      (Over.pullback (jK V₁)).map F = U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv := fun u => by
    haveI := hf u
    exact (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) G G₀ hG hsa (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv)).exists
  choose q hq hq' using hext
  have hcomp : ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α =
      (U.gen.hom ≫ pr u).left ≫ φc := by
    intro u
    rw [hq' u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left]
    rw [hκα]
  have hsa8 : IsSemiAbelian (powObj G₀ 8) :=
    GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8) hsa
  have hPi := prod_of_isLimit (powIsLimit G₀ 8)
  obtain ⟨Q, hQ, -⟩ := hPi G q
  have hmul : ∀ (T : Over (Sp V₁)) (x y : T ⟶ G), (x * y) ≫ Q = (x ≫ Q) * (y ≫ Q) := fun T x y =>
    (hPi T fun u => (x * y) ≫ q u).unique (fun u => by rw [Category.assoc, hQ u]) (fun u => by
      haveI := hq u
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hQ u, MonObj.mul_comp])
  haveI hQm : IsMonHom Q := by
    constructor
    · have h := hmul _ (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) 1
      rw [_root_.mul_one] at h
      have h' : (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) ≫ Q = 1 := mul_eq_left.1 h.symm
      simpa [Hom.one_def] using h'
    · have h := hmul (G ⊗ G) (fst _ _) (snd _ _)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
      rw [h]; congr 1
  have hGK := prod_postcomp (κ ≪≫ U₀.gen.symm) (prod_precomp U.gen hP)
  have hPiK := prod_pullback (jK V₁) hPi
  haveI : IsIso ((Over.pullback (jK V₁)).map Q) :=
    isIso_of_prod hGK hPiK _ (fun u => by
      rw [← Functor.map_comp, hQ u, hq' u]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc])
  let e := asIso ((Over.pullback (jK V₁)).map Q)
  obtain ⟨Q', hQ'm, hQ'⟩ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) (powObj G₀ 8) G hsa8 hG e.inv).exists
  have e1 : Q ≫ Q' = 𝟙 G := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) G G hG hG (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.hom_inv_id⟩
    ⟨inferInstance, (Over.pullback _).map_id G⟩
  have e2 : Q' ≫ Q = 𝟙 _ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) (powObj G₀ 8) (powObj G₀ 8) hsa8 hsa8 (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.inv_hom_id⟩
    ⟨inferInstance, (Over.pullback _).map_id _⟩
  let E : G ≅ powObj G₀ 8 := ⟨Q, Q', e1, e2⟩
  refine ⟨q, hq, fun T' y' => ?_, hcomp⟩
  obtain ⟨x, hx, hu⟩ := prod_precomp E hPi T' y'
  exact ⟨x, fun u => by rw [← hQ u]; exact hx u, fun x' hx' => hu x' fun u => by
    change x' ≫ Q ≫ powPr G₀ u = y' u
    rw [hQ u]; exact hx' u⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_isPow_model | exact GlobalTheory.Poinc.Sep.unif_pow_isPow_model | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_isPow_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatriStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  first | exact @GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | exact GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | (intros; apply GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowEq

theorem endU_exists (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (hCN : IsCN V₁)
    (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal V₁) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : EndU U.toUnifPre, E.aA = aA := by
  have hadm : AdmBase V₁ (maximalIdeal V₁) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  haveI := hCN.1
  haveI := hCN.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
    (FractionRing V₁) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase V₁ (maximalIdeal V₁) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_of_matrix : ∀ (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) → ∀ (f : X ⟶ X) (a : Matrix (Fin 8) (Fin 8) ℤ), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → IsMonHom f := by
  intro S X Y _ _ _ pr hpr hu f a hf
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

end GlobalTheory.Poinc.Sep.PowEq


open GlobalTheory.Poinc.Sep.PowEq in
theorem GlobalTheory.Poinc.Sep.unif_pow_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P c hc pr hpr hpru hPL G _ _ hG D U
  obtain ⟨φc, φ₂, hφc, hsq', hlb', hlev⟩ := hc
  obtain ⟨q, hq, hqu, hqc⟩ := GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr hpru G hG D U
  obtain ⟨e, hS, heq⟩ := GlobalTheory.T.eighthPowerDegData_latticeIso_equivariant g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P c
    φc φ₂ hφc hsq' hlb' hlev pr hpr hpru hPL G hG D U q hq hqu hqc
  refine ⟨e, hS, fun a a' ha aA haA => ?_⟩
  obtain ⟨E, hE⟩ := endU_exists V₁ hCN D P G hG U aA (isMonHom_of_matrix _ P.A c.A pr hpr hpru aA a haA)
  refine ⟨E, hE, heq a a' ha E (GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr G hG D U q hq hqc
    a E ?_)⟩
  rw [hE]
  exact haA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariantStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisation_eighthPower_data_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_equivariant | exact GlobalTheory.Poinc.Sep.unif_pow_equivariant | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_equivariant <;> assumption)
end
end
