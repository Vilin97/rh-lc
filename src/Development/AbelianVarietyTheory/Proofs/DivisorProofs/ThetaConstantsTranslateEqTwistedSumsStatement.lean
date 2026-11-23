module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt

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

namespace GlobalTheory.GSep.GMem

theorem exists_yy : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 mu
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

end GlobalTheory.GSep.GMem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen

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

namespace GlobalTheory.GSep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil_gen : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  intro I X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 τ χ hχ hpt a mu hY
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
    rw [(eq_gtExt_iff _ hf _ _).2 hext.2, hpg]
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

end GlobalTheory.GSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember

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

theorem GlobalTheory.GSep.twistAtEach_exists : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.GSep.torusChar_eq_weil_gen I X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.GSep.TorPt.exists_torus_char I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.GSep.TwistTranslate.twistSum_translate I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)
    (GlobalTheory.GSep.GMem.exists_yy I X₁ z₁ act V ev X t δ 𝔪) (hsg V ev X t δ 𝔪 τ χ hχN hχo) he⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement

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


theorem _root_.GlobalTheory.T.exists_twisted_theta_sum_common_sign_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  first | exact @GlobalTheory.GSep.twistAtEach_exists | exact GlobalTheory.GSep.twistAtEach_exists | (intros; apply GlobalTheory.GSep.twistAtEach_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums

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

theorem GlobalTheory.GSep.exists_stalk_zeta (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem GlobalTheory.GSep.twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_twisted_theta_sum_common_sign_member I X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X)
      (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : X → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dite_eq_left hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member I X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dite_eq_right hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := GlobalTheory.GSep.exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaConstants_translate_eq_twisted_sums : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  first | exact @GlobalTheory.GSep.twistSum_translate | exact GlobalTheory.GSep.twistSum_translate | (intros; apply GlobalTheory.GSep.twistSum_translate <;> assumption)
end
end
