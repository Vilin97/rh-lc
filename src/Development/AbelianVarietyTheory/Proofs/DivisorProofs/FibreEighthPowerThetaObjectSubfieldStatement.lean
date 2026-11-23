module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalizationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibThetaMove

open GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtUp GlobalTheory.UMin.ThMove

theorem exists_gen_thG_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  intro V₁ _ _ D K _ _ ev o _ g m J b s t ψ hψ hLB v H
  obtain ⟨w, hw⟩ := hLB
  have := t.ab.comm
  have := D.P.isAb.comm
  let F := (Over.pullback (spMap ev)).obj D.P.A
  have : IsCommMonObj F := Functor.isCommMonObj_obj
  let φF := pullback.fst D.P.A.hom (spMap ev)
  have hpD : IsGrpPullback F D.P.A (spMap ev) φF := isGrpPullback_pullback D.P.A (spMap ev)
  have hLD : D.P.L.IsLB := D.P.isLB
  have hLF : (D.P.L.pull φF).IsLB := pull_isLB hLD φF
  have hLt : t.L.IsLB := t.isLB
  have hw₁ : (idIso (D.P.L.pull φF)).IsGen := idIso_isGen hLF
  obtain ⟨ρF, hρF, hrF⟩ := exists_rigidificationPullbackCompatibleIso (w := idIso (D.P.L.pull φF)) (ρ₀ := D.rig) hpD hw₁ hLD hLF D.rig_gen

  have hE : eSec F ≫ ψ = 𝟙 _ ≫ eSec t.A := by
    have := over_one hψ (T := baseOver _) (T₀ := baseOver _) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (𝟙 _ ≫ ·) (Category.id_comp _)))
  obtain ⟨ρt, hρt, hrt'⟩ := exists_gen_up_iso (K := PUnit) (φ' := fun _ => eSec F) (φ := fun _ => eSec t.A)
    (ε := fun _ => 1) (h := 𝟙 _) (χ := 𝟙 _) hw hLt hLF (Category.id_comp _) (Category.id_comp _) (fun _ => hE) ρF hρF
  have hrt : IsRigidificationPullbackCompatibleIso w (𝟙 _) ρF ρt := fun Z r z J J' hJ hJ' =>
    (hrt' Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])

  let x : Ix g (m ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) := fun a =>
    (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ a, x a ^ (m ^ 2) = 1 := fun a => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a) ^ (m ^ 2) = 1
    rw [← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨tht, hgt, hTt⟩ := exists_gen_thG_of_isThetaPt K t.pol ρt hρt m (Ix g (m ^ 2)) x v hx H

  have hτ₁ : 𝟙 (Sp K) ≫ (baseOver (Sp K)).hom = (baseOver (Sp K)).hom ≫ 𝟙 (Sp K) := by simp
  choose xF hxF hnF using fun a => torsion_down hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ (x a) (hx a)
  obtain ⟨thF, hsF⟩ := exists_secRel hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ hw hLt hLF tht
  have hgF := isGenSec_down hψ (𝟙 _) hτ₁ hw hLt hLF hsF hgt
  have hTF := fun a =>
    ThG.move hψ (𝟙 _) hτ₁ hw hLt hLF hrt (hxF a) (hnF a) hsF (hTt a)

  have hτ₂ : 𝟙 (Sp K) ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := by simp
  choose x₀ hx₀ hn₀ using fun a => torsion_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ (xF a) (hnF a)
  obtain ⟨th₀, hs₀⟩ := exists_secRel_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF thF
  have hg₀ : IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th₀ := isGenSec_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hs₀ hgF
  refine ⟨th₀, 1, hg₀, one_ne_zero, fun a => ⟨x₀ a, ?_⟩⟩
  have q := ThG.up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hrF (hx₀ a) (hn₀ a) hs₀ (hTF a)
  simpa using q

end GlobalTheory.FibThetaMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  first | exact @GlobalTheory.FibThetaMove.exists_gen_thG_fibre | exact GlobalTheory.FibThetaMove.exists_gen_thG_fibre | (intros; apply GlobalTheory.FibThetaMove.exists_gen_thG_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit : ∀ (n : ℕ), n.Prime → Odd n → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (n : V₁) →
  ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen →
  ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th →
  ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K),
    GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit | exact GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit | (intros; apply GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementCoefficientFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem fibre_theta_consts_in_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  intro W _ gQ J l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q _ ρ _ D e _ C u mo hmo hT K _ _ ev k₀ hk₀ hrat bT t ψ hψ hL
  haveI : IsAlgClosed k₀ := hk₀
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 hlo.pow t K (𝟙 _)
  obtain ⟨th, κ, hth, hκ, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_fibre V₁ D K ev k₀ (8 * gQ) (l ^ j) J bT _ t ψ hψ hL v₀ hv₀
  obtain ⟨M, lam, hM, hA⟩ := GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit l hl hlo j hj V₁ hCN hlu D _ C e u mo hmo hT K ev D.rig D.rig_gen th hth
  obtain ⟨c', hc'⟩ := (hmo 0).2
  have hev : ev (u 0 c') ≠ 0 := (hc'.map ev).ne_zero
  have key : ∀ a, ∃ w : K, w ∈ k₀ ∧ κ * v₀ a = lam * ev (u 0 c') * w := by
    intro a
    obtain ⟨y, hya⟩ := hy a
    obtain ⟨c₀, ζ, hζ, hc⟩ := hA y _ hya
    obtain ⟨r, hr, hr'⟩ := hrat 0 c₀ c' hc'
    have hζk : ζ ∈ k₀ := Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
    exact ⟨ζ * r, k₀.mul_mem hζk hr, by rw [hc, hr']; ring⟩
  choose w hw hkw using key
  by_cases hlam : lam = 0
  · refine ⟨fun _ => 0, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ 1 isUnit_one (fun a => ?_) hv₀
    have := hkw a
    rw [hlam, zero_mul, zero_mul] at this
    simp [(mul_eq_zero.1 this).resolve_left hκ]
  · refine ⟨fun a => ⟨w a, hw a⟩, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ ((lam * ev (u 0 c'))⁻¹ * κ)
      (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero (mul_ne_zero hlam hev)) hκ)) (fun a => ?_) hv₀
    show w a = _
    rw [_root_.mul_assoc, hkw a, ← _root_.mul_assoc, inv_mul_cancel₀ (mul_ne_zero hlam hev), _root_.one_mul]

end GlobalTheory.Poinc.Sep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementCoefficientFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharp_refinement_coefficient_family : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  first | exact @GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield | exact GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield | (intros; apply GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_theta_object : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨J, hJ, Mat, κ, w, w', hA⟩ := GlobalTheory.T.sharp_refinement_odd_prime_localization W hW gQ
  refine ⟨J, hJ, Mat, κ, w, w', ?_⟩
  intro l hl ho j hj V V₁ _ _ _ _ _ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨bT, t, ψ, h1, h2, h3, h4, h5⟩ := hA l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS K ev k₀ hk₀
  obtain ⟨v, hv⟩ := GlobalTheory.T.sharp_refinement_coefficient_family W hW gQ J l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr bT t ψ h3 h4
  exact ⟨bT, t, v, ψ, h1, h2, hv, h3, h4, h5⟩

end GlobalTheory.Poinc.Sep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.fibre_eighth_power_theta_object_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | exact GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_theta_object <;> assumption)
end
end
