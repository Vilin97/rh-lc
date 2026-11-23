module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormalStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValOfUnitMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantValueNeZero

section

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem UMem.exists_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type)
    [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ)
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ),
    ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.Poinc.Sep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantValueNeZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_thetaConstant_value_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  first | exact @GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | exact GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | (intros; apply GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UMemBaseChangeValues

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemBC
open GlobalTheory.ArcPull

theorem uMem_baseChange_values : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' → Function.Injective j → IsLocalHom j → (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) → ∃ 𝔫 : UMem X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ, (∀ r, 𝔫.yK r = k (𝔪.yK r)) ∧ ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ j k hV' hj hl hkv
  have hkj : k = fracMap hj := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun v => ?_)
    exact (hkv v).trans (fracMap_algebraMap hj v).symm
  have hV := 𝔪.cn
  have hAd : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hAd' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have hI : (maximalIdeal V).map j ≤ maximalIdeal V' := map_maximalIdeal_le j
  obtain ⟨D', hD, A', gA, U', hPU, hgA, htA, hrel⟩ := exists_pull_gen hAd hAd' j hj hI 𝔪.semi 𝔪.U
  have hwl : LBIso A'.L (X₁.ρ.P.L.pull (gA ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) htA (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ gA)
  obtain ⟨wl, hwl⟩ := hwl
  haveI := 𝔪.loc
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  refine ⟨{
    cn := hV'
    loc := inferInstance
    reg := regAt_comp X₁ z₁ ev j hj 𝔪.reg
    yK := (fracMap hj).comp 𝔪.yK
    yK_eq := yK_comp X₁ z₁ ev j hj 𝔪.yK 𝔪.yK_eq
    D := D'
    e₈ := 𝔪.e₈.trans hD.xe.symm
    G := (Over.pullback (specOf j)).obj 𝔪.G
    semi := IsSemiAbelian.pullback _ _ 𝔪.semi
    A := A'
    U := U'
    φ := gA ≫ 𝔪.φ
    cart := (hgA.comp 𝔪.cart).congr (by rw [spMap_comp]) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a a' ha => ?_
    psi := fun mu => ?_ }, fun r => ?_, ?_⟩
  · obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' ha
    have := E.homG
    obtain ⟨E', h1, h2, -⟩ := EndBaseChange.exists_end hD hPU E ((Over.pullback (specOf j)).map E.aG)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    refine ⟨E', ?_, fun mu => ?_⟩
    · rw [← Category.assoc, aA_comm j hj 𝔪.U.toUnifPre U'.toUnifPre gA hgA hrel E E' h1, Category.assoc, hE1,
        Category.assoc]
    · apply hD.xe.injective
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, h2, hE2]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hr : Formalism.L2.Pj.PsiCoord 𝔪.D.toPre (hD.xe (hD.xe.symm (𝔪.e₈ mu))) (u * mono W t δ mu) := by
      rw [AddEquiv.apply_symm_apply]; exact hu
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ hr
    refine ⟨u' * Units.map j.toMonoidHom u, ?_⟩
    have hm : mono W (fun i => j (t i)) δ mu = j (mono W t δ mu) := by simp [mono, map_prod, map_pow]
    convert hu' using 1
    · exact AddEquiv.trans_apply _ _ _
    · rw [hm, map_mul]
      simp [_root_.mul_assoc]
  · show fracMap hj (𝔪.yK r) = k (𝔪.yK r)
    rw [hkj]
  · rintro a mu ⟨p, x, hpy, hqx, hxφ⟩
    obtain ⟨p', x', σ, hσ, hp'y, hq', hx'⟩ := yy_pull' hV hV' j hj hl 𝔪.semi 𝔪.U D' hD A' gA U' hPU hgA hrel _ hk p x hqx
    refine ⟨p', x', ?_, hq', ?_⟩
    · show p'.y = (𝔪.e₈.trans hD.xe.symm) mu
      rw [AddEquiv.trans_apply, hp'y, hpy]
    · show x'.left ≫ gA ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))).comp
          ((fracMap hj).comp 𝔪.yK)) ≫ (X₁.ρ.pt a).left
      rw [← Category.assoc, hx', Category.assoc, hxφ, ← Category.assoc, ← spMap_comp]
      congr 2
      rw [← RingHom.comp_assoc, hσ, RingHom.comp_assoc]

end GlobalTheory.Poinc.Sep.MemBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantLeCommonBoundMonomial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.DivBound

theorem theta_pow_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w)) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 ν h1 h2 c hc a
  obtain ⟨yy1, -, yy3, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  by_cases hm : maximalIdeal V = ⊥
  · obtain ⟨w, hw⟩ := yy1 a
    refine ⟨w, hw, ?_⟩
    have hu : IsUnit (mono W t δ w) := by
      by_contra hn
      exact 𝔪.mono_ne_zero w ((Submodule.mem_bot V).1 (hm ▸ (mem_maximalIdeal _).2 hn))
    have h1' : ν (algebraMap V (FractionRing V) (mono W t δ w)) = 1 := by
      refine le_antisymm (h1 _) ?_
      have e : ν (algebraMap V (FractionRing V) (mono W t δ w)) * ν (algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ)) = 1 := by
        rw [← map_mul, ← map_mul, hu.mul_val_inv, map_one, map_one]
      calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
        _ ≤ ν (algebraMap V (FractionRing V) (mono W t δ w)) * 1 := mul_le_mul' le_rfl (h1 _)
        _ = _ := _root_.mul_one _
    rw [h1', _root_.mul_one]
    exact pow_le_pow_left' (hc a) _
  · obtain ⟨V', _, _, _, _, j, k, hcn, hj, hjl, hk, hν⟩ := GlobalTheory.DivBound.exists_cdvr_valuation_le V 𝔪.cn ν h1 h2 hm
    obtain ⟨𝔫, hyk, hyy⟩ := GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange_values g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 V' j k hcn hj hjl hk
    obtain ⟨b, hb⟩ := GlobalTheory.Poinc.IntTerm.DvrScale.exists_dvd_pow g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫
    obtain ⟨w, r, hw, he⟩ := hb a
    obtain ⟨mu, hmu⟩ := yy1 a
    have hn3 := (GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫).2.2.1
    have hw' : 𝔪.YY a w := (yy3 a mu w hmu).2 ((hn3 a mu w (hyy a mu hmu)).1 hw)
    refine ⟨w, hw', ?_⟩
    have hmono : mono W (fun i => j (t i)) δ w = j (mono W t δ w) := by
      simp [mono, map_prod, map_pow]
    have key := hν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))
      (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w))
      ⟨r, by rw [map_pow, ← hyk, he, map_mul, map_pow, ← hyk, hk, hmono]; ring⟩
    rw [map_pow, map_mul, map_pow] at key
    exact key.trans (mul_le_mul' (pow_le_pow_left' (hc b) _) le_rfl)

end GlobalTheory.Poinc.Sep.DivBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantLeCommonBoundMonomialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaConstant_le_commonBound_monomial : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w))) := by
  first | exact @GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | exact GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | (intros; apply GlobalTheory.Poinc.Sep.DivBound.theta_pow_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelClassZeroOfDividesAllThetaConstants

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DivInt

theorem ratio {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} (ha : X₁.M.Div X₁.S.th a z₁) (b : X₁.S.Gam) :
    ∃ v : V, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ = algebraMap V (FractionRing V) v * 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC
  have hC : yC (closedPoint V) ⤳ z₁ := sp _
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hξz : ξ ⤳ z₁ := sp _
  have hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁ := ha.2 b
  have hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz hr
  have haξ : X₁.S.th a ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem a)
  refine ⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩
  have e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a := (div_mul_cancel₀ _ ha.1).symm
  have e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩) :=
    RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)
  rw [← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]

theorem label_zero_of_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 a ha
  have ha' : X₁.M.Div X₁.S.th a z₁ := ha
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.exists_thetaConstant_value_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  have hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b₀
    rw [h0, mul_zero] at hv
    exact hb₀ hv
  obtain ⟨ν, hν1, hνm⟩ := GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn
  have hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun b => by
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b
    rw [hv, map_mul]
    exact mul_le_of_le_one_left' (hν1 v)
  obtain ⟨w, hw, hle⟩ := GlobalTheory.T.thetaConstant_le_commonBound_monomial g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 ν hν1 hνm _ hmax a
  have h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)
  have h1 : 1 ≤ ν (algebraMap V (FractionRing V) (mono W t δ w)) := by
    have := mul_le_mul_of_nonneg_left hle
      (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul] at this
  by_cases hw0 : w = 0
  · exact hw0 ▸ hw
  · exact absurd h1 (not_le.2 (hνm _ (𝔪.mono_mem hw0)))

end GlobalTheory.Poinc.Sep.DivInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelClassZeroOfDividesAllThetaConstantsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaLabel_class_zero_of_divides_all_thetaConstants : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  first | exact @GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI | exact GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI | (intros; apply GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI <;> assumption)
end
end
