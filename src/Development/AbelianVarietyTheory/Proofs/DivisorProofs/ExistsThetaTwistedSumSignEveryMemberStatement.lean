module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPowStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFraStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeil

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ χ hχ hpt a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hK : KerPowSt := hL.1.kerPow
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p, x, hpy, hpg, hpx, hxo⟩ := hpt (torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ))
    ((isTor_iff _ _).2 (isTorusPtF_torusPt χ))
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  obtain ⟨p₁, hext, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p
  set χ₁ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ with hχ₁
  have hp₁g : p₁.g = torusPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (Additive.ofMul χ₁) := by
    have hg := (eq_gtExt_iff (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p.g p₁.g).2 hext.2
    rw [hg, hpg]
    exact gtExt_torusPt _ hf χ
  have hp₁y : p₁.y = 0 := hext.1.trans hpy
  have hτ₁ : IsTor χ₁ p₁.g := by rw [hp₁g]; exact (isTor_iff _ _).2 (isTorusPtF_torusPt χ₁)
  have W₁ := weilQkIs_tor hG p₁ p' hp₁y hτ₁
  have hx₁ := (qkToAkU_iff_of_algebra hG hK 𝔪.U hk hext x).1 hpx
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk p₁ p' _ x' hx₁ hp'x (χ₁ (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    (fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x) x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [hχ₁, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [Units.val_one, one_smul]
    refine (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective ?_
    have hc : (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (eStd X₁.S.g _ τ a).val =
        algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ a).val)) := by
      simp only [pow_mul, map_pow]
    rw [e']
    exact congrArg (fun z => algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK z)) hc
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [Over.comp_left, Category.assoc, hxo]
    rfl
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.torsionFrames_sectionValues_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c → ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  first | exact @GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | exact GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | (intros; apply GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumTermsEqThetaConstantTranslate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem twistSum_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab _ T hT c τ _ χ hχ hyp
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, hval⟩ := GlobalTheory.T.torsionFrames_sectionValues_ratio_rootOfUnity V 𝔪.A ρA hρA _ (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) _ _ _
    (htors (lab c + τ)) he₂ th _ (hth (lab c + τ))
  have hsum := hov 1 le_rfl w'' (fun z J _ => (pow_one _).symm) hw''g th s _ hs hval
  obtain ⟨e, he⟩ := GlobalTheory.T.rootOfUnity_fractionField_member_eq_zeta_pow g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 u hu
  refine ⟨e, ?_⟩
  rw [← he]
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'' χ' =
      ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' => by
    rw [GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (c := 1) (fun z J _ => by rw [hw''v, map_one, _root_.one_mul]) s χ',
      _root_.one_mul]
  have hA := admissibleBase_of_completeNormalLocalCharZero 𝔪.cn
  have key := ((GlobalTheory.AdicSum.sumF_calculus V _ hA (FractionRing V) _
    (coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'') 0 _ 0).2.2 (Fin 8 → X) 𝔪.e₈
    𝔪.e₈.injective (fun j hj => absurd ⟨𝔪.e₈.symm j, 𝔪.e₈.apply_symm_apply j⟩ hj)).2 hsum
  convert key using 2 with mu
  simp only [Function.comp_apply, hco, hTc]

end GlobalTheory.Poinc.Sep.TwistTranslate
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumTermsEqThetaConstantTranslateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | exact GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | (intros; apply GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTwistedSumSignEveryMember

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistAtEach_exists : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.Poinc.Sep.torusChar_eq_weil g n F W Z i X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv)
    (GlobalTheory.Poinc.Sep.UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hsg V ev X m t δ 𝔪 τ χ hχN hχo) he⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTwistedSumSignEveryMemberStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  first | exact @GlobalTheory.Poinc.Sep.twistAtEach_exists | exact GlobalTheory.Poinc.Sep.twistAtEach_exists | (intros; apply GlobalTheory.Poinc.Sep.twistAtEach_exists <;> assumption)
end
end
