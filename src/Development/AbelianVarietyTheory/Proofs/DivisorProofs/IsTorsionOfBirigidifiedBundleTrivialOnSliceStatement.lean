module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneBirigidifiedSymmetricNoetherian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AbDual

theorem exists_pow_eq_one_of_triv_ev_noeth : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ M : ℕ, 0 < M ∧ ∀ (T : Over (Sp B)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ M = 1 := by
  intro B _ _ A _ _ P hA hP h0l h0r hsym hamp
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP _
  obtain ⟨H, _, i, hi, hm, hf, hfl, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup B A hA _ hL hamp
  haveI : IsCommMonObj H := GlobalTheory.AbelianImage.isCommMonObj_of_mono i
  obtain ⟨M, hM, h1⟩ := GlobalTheory.FiniteFlatKilled.main B H hf hfl
  refine ⟨M, hM, fun T x hx => ?_⟩
  obtain ⟨z, rfl⟩ := (hH T x).1 (memKL_diag_of_triv_ev_of_symm B A hA P hP h0l h0r hsym T x hx)
  have h2 : z ^ M = 1 := by
    rw [← Category.comp_id z, ← MonObj.comp_pow, h1, MonObj.comp_one]
  rw [← MonObj.pow_comp, h2, MonObj.one_comp]

end GlobalTheory.AbDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneBirigidifiedSymmetricNoetherianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ M : ℕ, 0 < M ∧ ∀ (T : Over (Sp B)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ M = 1 := by
  first | (exact @GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (exact GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (intros; apply GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSlice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.KerTorsion

open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_pow_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (B : Type) [CommRing B] (y : Sp B ⟶ S) (x : Over.mk y ⟶ A), (∃ t : (P.pull (lift (snd A (Over.mk y) ≫ x) (fst A (Over.mk y))).left).Gen, t.IsGen) → ∃ M : ℕ, 0 < M ∧ x ^ M = 1 := by
  intro S A _ _ P ab hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ symm ample B _ y x ⟨t, ht⟩
  let A' := (Over.pullback y).obj A
  let φ := PullbackComparison.pφ y A
  let φ₂ := PullbackComparison.pφ₂ y A
  have pb : IsGrpPullback A' A y φ := PullbackComparison.isGrpPullback y A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare y A
  have hab : IsAbelianScheme A' :=
    { comm := inferInstance
      smooth := by have := ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  let P' : LB (G2 A').left := P.pull φ₂
  have hP' : P'.IsLB := pull_isLB hP φ₂
  have iso : LBIso P' (P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  obtain ⟨B₀, A₀, _, _, ψ, ψ₂, P₀, fin, ab₀, pb₀, sq₀, hP₀, iso₀, r₁, r₂, symm₀, ample₀⟩ :=
    GlobalTheory.T.polarised_abelian_scheme_descends_finite_type B A' P' hab hP'
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id y A)) t₁ ht₁)
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one y A)) t₂ ht₂)
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
        (chartPullLinComb P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap y A)) symm)
      ((pol_pull S _ A A' y φ _ _ (pull_isLB hP _) (pull_isLB hP' _) ab pb dg).2.1 ample)
  have : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing ℤ B₀
  obtain ⟨M, hM, hker⟩ := GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian B₀ A₀ P₀ ab₀ hP₀ r₁ r₂ symm₀ ample₀
  refine ⟨M, hM, ?_⟩
  let T : Over (Sp B) := Over.mk (𝟙 _)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb T y (Category.id_comp _).symm
  have hx : x.left = (e.symm x).left ≫ φ := by rw [← he, e.apply_symm_apply]
  have key : e.symm x ^ M = 1 := by
    refine GlobalTheory.HTPull.kernel_pullback pb₀ sq₀ hP₀ hP' iso₀ M hker T (e.symm x) ?_
    have w : ((fst A' T).left ≫ φ) ≫ A.hom = (snd A' T).left ≫ y := by
      rw [Category.assoc, pb.1.w, ← Category.assoc, Over.w (fst A' T), ← Over.w (snd A' T)]
      exact congrArg (· ≫ y) (Category.comp_id _)
    let χ : (A' ⊗ T).left ⟶ (A ⊗ Over.mk y).left := pullback.lift _ _ w
    have c₁ : χ ≫ (fst A (Over.mk y)).left = (fst A' T).left ≫ φ := pullback.lift_fst _ _ _
    have c₂ : χ ≫ (snd A (Over.mk y)).left = (snd A' T).left := pullback.lift_snd _ _ _
    refine gen_chartPull (chartPullLinComb P _ _ _ _ χ fun _ => ?_) t ht
    refine (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((A' ⊗ T).hom ≫ y))
      (T' := A' ⊗ T) (𝟙 _) _ _ (Z := A ⊗ Over.mk y) χ _ _ ?_ ?_)
    · rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← hx, ← Category.assoc χ, c₂]
    · rw [Category.id_comp, c₁]
  rw [← e.apply_symm_apply x, ← map_pow, key, map_one]

end GlobalTheory.KerTorsion
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSliceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (B : Type) [CommRing B] (y : Sp B ⟶ S) (x : Over.mk y ⟶ A), (∃ t : (P.pull (lift (snd A (Over.mk y) ≫ x) (fst A (Over.mk y))).left).Gen, t.IsGen) → ∃ M : ℕ, 0 < M ∧ x ^ M = 1 := by
  first | (exact @GlobalTheory.KerTorsion.exists_pow_eq_one) | (exact GlobalTheory.KerTorsion.exists_pow_eq_one) | (intros; apply GlobalTheory.KerTorsion.exists_pow_eq_one <;> assumption)
end
end
