module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfExtendsOverCompleteDvrs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveTheta

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmDvr

theorem exists_unit_of_prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {J : Type}
    {c : J → FractionRing V} (b : FractionRing V) (hc : Prim (algebraMap V (FractionRing V)) c)
    (hb : Prim (algebraMap V (FractionRing V)) (fun j => b * c j)) :
    ∃ u : Vˣ, algebraMap V (FractionRing V) u = b := by
  obtain ⟨hc₁, j₀, hj₀, hj₀'⟩ := hc
  obtain ⟨hb₁, j₁, hj₁, hj₁'⟩ := hb
  have I1 : IsIntegral V b := by
    have := IsIntegral.mul (show IsIntegral V (b * c j₀) from hb₁ j₀) (show IsIntegral V (c j₀)⁻¹ from hj₀')
    rwa [_root_.mul_assoc, mul_inv_cancel₀ hj₀, _root_.mul_one] at this
  have hcne : c j₁ ≠ 0 := right_ne_zero_of_mul hj₁
  have I2 : IsIntegral V b⁻¹ := by
    have := IsIntegral.mul (show IsIntegral V (c j₁) from hc₁ j₁) (show IsIntegral V (b * c j₁)⁻¹ from hj₁')
    rwa [mul_inv, mul_left_comm, mul_inv_cancel₀ hcne, _root_.mul_one] at this
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 I1
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 I2
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hj₁
  have hvw : v * w = 1 := IsFractionRing.injective V (FractionRing V) (by
    rw [map_mul, hv, hw, mul_inv_cancel₀ hb0, map_one])
  exact ⟨⟨v, w, hvw, by rw [mul_comm, hvw]⟩, hv⟩

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    {g : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hp, hw⟩ := h
  have hN := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) hp t.PP.isLB P.isLB hN
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hN⟩ hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 P.isAb.proper,
    amplePt _ _ _ _ _ _ hφ _ _ P.isLB hN e P.ample P.ktriv⟩

end GlobalTheory.UMin.OmDvr



open GlobalTheory.UMin.OmDvr in
theorem GlobalTheory.UMin.exists_sec_nz_of_prim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  intro E _ _ _ H S t g m N V _ _ _ hV χ θ pt c hm h3 hu hP hT hc
  have hL := t.PP.isLB
  have : IsDiscreteValuationRing V := hV.1
  have := t.semi.comm
  have hpa := GlobalTheory.UMin.OmDvr.polAt_of_polFib t hP
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull χ t
  have hp' := GlobalTheory.SplitPoint.polAt_pullback m₁ hpa (jK V) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨σ₀, hσ₀⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H S t V χ _ m₁ hp'
  have h0V : spMap (RingHom.id V) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
  have hNZ := hσ₀ V (RingHom.id V) χ h0V
  obtain ⟨P, α, hg, hp, hw⟩ := hP
  have hx0 : spMap (RingHom.id (FractionRing V)) ≫ (spMap (algebraMap V (FractionRing V)) ≫ χ) =
      spMap (algebraMap V (FractionRing V)) ≫ χ :=
    (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp (FractionRing V)) t.G t.PP.L hL P _ α hp hw
    (FractionRing V) (𝟙 _) _ (Category.id_comp _)
  obtain ⟨a, ha⟩ := he.ex (RingHom.id _) hx0 (SecM.ofSec t.G θ)
  generalize VVRank.pullS t.G _ (Over.homMk (spMap (RingHom.id V)) h0V : Over.mk χ ⟶ Over.mk χ) σ₀ = σ₁ at hNZ
  obtain ⟨s, hs⟩ := he.ex (RingHom.id _) hx0 (pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁))
  have hmK : ((m : ℕ) : FractionRing V) ≠ 0 := by
    have := (hu.map (algebraMap V (FractionRing V))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨j₀, hj₀, -⟩ := hc.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h00 : SecM.ofSec t.G θ = @id Γ((Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ)).left, ⊤)
        (GlobalTheory.ZH.fn (0 : FractionRing V)) • SecM.ofSec t.G θ := by
      change _ = fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) 0 • _
      rw [map_zero, zero_smul, ha, map_zero, zero_smul]
    have q := (GlobalTheory.UMin.thG_smul_iff S t.G t.PP.L t.PP.rig hL t.PP.rigGen g m (FractionRing V) _ θ θ (pt j₀) 0 (c j₀) (c j₀) hm
      hmK ⟨P, α, hg, hp, hw⟩ h00 (hT.2.1 j₀)).1 (hT.2.1 j₀)
    exact hj₀ (by simpa using q)

  have hrel : pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁) =
      fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) (s * a⁻¹) • SecM.ofSec t.G θ := by
    have key : s = (s * a⁻¹) * a := by rw [_root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]
    rw [hs, ha, smul_smul, ← map_mul, ← key]
  have hT' : ThList t.G t.PP.L t.PP.rig m (spMap (algebraMap V (FractionRing V)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ₁ (algebraMap V (FractionRing V))) pt (fun j => (s * a⁻¹) * c j) := by
    refine ⟨hT.1, fun j => ?_, hT.2.2⟩
    show ThG t.G t.PP.L t.PP.rig m _ (pt j) (fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) ((s * a⁻¹) * c j))
    rw [map_mul]
    exact ThG.smul hL hrel (hT.2.1 j)
  have hprim := GlobalTheory.UMin.prim_of_polFib E H S t g V hV χ ⟨P, α, hg, hp, hw⟩ _ hNZ m N hm h3 hu (FractionRing V)
    (algebraMap V (FractionRing V)) pt _ (IsFractionRing.injective V (FractionRing V)) hT'
  obtain ⟨u, hu'⟩ := exists_unit_of_prim (s * a⁻¹) hc hprim
  have hpull : pl (algebraMap V (FractionRing V)) rfl (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁) = SecM.ofSec t.G θ := by
    rw [pl_smul, hrel, smul_smul, ← map_mul, ← hu', ← map_mul, Units.inv_mul, map_one, map_one, one_smul]
  refine ⟨SecM.toSec t.G (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁), hpull, ?_⟩
  obtain ⟨g₀, h₁, h₂⟩ := hNZ
  refine ⟨g₀, h₁, ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₂
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  change g₀ ∈ Scheme.basicOpen _ (liftHom t.G _ (fnR χ (u⁻¹ : Vˣ).val) * σ₁.f k)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (((u⁻¹).isUnit.map (fnR χ)).map (liftHom t.G _))]
  exact ⟨Scheme.basicOpen_le _ _ hk, hk⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveThetaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  first | exact @GlobalTheory.UMin.exists_sec_nz_of_prim | exact GlobalTheory.UMin.exists_sec_nz_of_prim | (intros; apply GlobalTheory.UMin.exists_sec_nz_of_prim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfExtendsOverCompleteDvrsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_of_extends_over_complete_dvrs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  first | exact @GlobalTheory.UMin.SecExtend.exists_sec_of_extends | exact GlobalTheory.UMin.SecExtend.exists_sec_of_extends | (intros; apply GlobalTheory.UMin.SecExtend.exists_sec_of_extends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSectionExtendsNonzeroOfIntegralThetaConstan

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmExt

theorem thList_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {x y : Sp K ⟶ S} (e : x = y) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) (H : ThList G L ρ m x θ pt c) : ∃ pt' : Fin N → (Over.mk y ⟶ G), ThList G L ρ m y (e ▸ θ) pt' c := by
  subst e; exact ⟨pt, H⟩

theorem inj_comp {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem exists_fracMap {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsFractionRing.lift (inj_comp φ hφ), RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩

theorem secAt_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R : Type} [CommRing R] {x : Sp R ⟶ S}
    {τ₁ τ₂ : SecAt G L x} (h : SecM.ofSec G τ₁ = SecM.ofSec G τ₂) : τ₁ = τ₂ :=
  ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val h) j

theorem cast_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {Z : Scheme.{0}} {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {y₁ y₂ : Z ⟶ S} (e : y₁ = y₂) (u₁ : Over.mk y₁ ⟶ T) (u₂ : Over.mk y₂ ⟶ T)
    (hu : u₁.left = u₂.left) :
    SecM.ofSec G (VVRank.pullS G _ u₂ σ) = SecM.ofSec G (e ▸ VVRank.pullS G _ u₁ σ) := by
  subst e
  obtain rfl : u₁ = u₂ := Over.OverMorphism.ext hu
  rfl

theorem pull_pull_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R V K K' : Type} [CommRing R]
    [CommRing V] [CommRing K] [CommRing K'] (χ : Sp R ⟶ S) (σ : SecAt G L χ) (φ : R →+* V) (a : R →+* K)
    (b : V →+* K') (φK : K →+* K') (h : spMap φK ≫ spMap a ≫ χ = spMap b ≫ spMap φ ≫ χ)
    (hc : φK.comp a = b.comp φ) :
    SecM.ofSec G (SecAt.pull G L (SecAt.pull G L σ φ) b) = SecM.ofSec G (h ▸ SecAt.pull G L (SecAt.pull G L σ a) φK) := by
  simp only [SecAt.pull]
  rw [ThetaRuleCompare.pullS_comp, ThetaRuleCompare.pullS_comp]
  refine cast_pullS G L σ h _ _ ?_
  simp only [Over.comp_left, Over.homMk_left]
  rw [← spMap_comp, ← spMap_comp, hc]

theorem secAt_eq_of_generic {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) {V : Type}
    [CommRing V] [IsDomain V] (x : Sp V ⟶ S) (τ₁ τ₂ : SecAt G L x)
    (h : SecAt.pull G L τ₁ (algebraMap V (FractionRing V)) = SecAt.pull G L τ₂ (algebraMap V (FractionRing V))) :
    τ₁ = τ₂ := by
  have hDom : IsDominant (spMap (algebraMap V (FractionRing V))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).trans_le bot_le)⟩
  have hSD : IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    (isSchemeTheoreticallyDominant_iff_isDominant _).2 hDom
  have hFl : Flat (fst (Over.mk x) G).left := inferInstanceAs (Flat (pullback.fst x G.hom))
  let ιK : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ Over.mk x :=
    Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
  have hP := ThetaRuleCompare.isPullback_whisker (A := G) ιK
  refine ThetaRuleCompare.sec_ext fun j => BundleExt.fn_ext_dense (spMap (algebraMap V (FractionRing V)))
    (fst (Over.mk x) G).left fun Z ρ r z hrz hz => ?_
  let ρ' : Z ⟶ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⊗ G).left := hP.lift ρ r hrz.symm
  have hfac : ρ' ≫ (ιK ▷ G).left = ρ := hP.lift_fst _ _ _
  have hz' : ρ' z ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x))).U j :=
    ThetaRuleCompare.chart_ge ιK j (show (ιK ▷ G).left (ρ' z) ∈ _ by rw [← Scheme.Hom.comp_apply, hfac]; exact hz)
  rw [← hfac, ← ThetaRuleCompare.gs_pullS ιK τ₁ ρ' z j hz', ← ThetaRuleCompare.gs_pullS ιK τ₂ ρ' z j hz']
  exact congrArg (fun u : SecAt G L (spMap (algebraMap V (FractionRing V)) ≫ x) => gs ρ' z _ (u.f j)) h

open GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace in
theorem mem_nonzeroLocus_of_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) (th : LB.Sec (LPow G L a T)) (z : (T' ⊗ G).left) (hz : z ∈ nonzeroLocus (VVRank.pullS G a h th)) :
    (h ▷ G).left z ∈ nonzeroLocus th := by
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ z).1 hz
  have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => a) th (h ▷ G).left
    (fun _ => whisker_snd_left G h) (𝟙 _) z j hj
  rw [Category.id_comp] at q
  have q' := q.trans (gs_stalkMap (h ▷ G).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left G h) j hj) _)
  refine (mem_nonzeroLocus _ _).2 ⟨j, wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T G).left) _
    (fun _ => whisker_snd_left G h) j hj, ?_⟩
  exact (isUnit_map_iff _ _).1 (q' ▸ u)

theorem spMap_closedPoint {R : Type} [CommRing R] (s : PrimeSpectrum R) {V : Type} [CommRing V] [IsLocalRing V]
    (φ₀ : Localization.AtPrime s.asIdeal →+* V) [IsLocalHom φ₀] :
    (spMap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal)))).base (IsLocalRing.closedPoint V) = s := by
  show PrimeSpectrum.comap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal))) (IsLocalRing.closedPoint V) = s
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint]
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  exact Localization.AtPrime.under_maximalIdeal

theorem om_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ χ θ pt c hodd h3 hm hPol hT hunit
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (φK : FractionRing R →+* FractionRing V)
      (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ),
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ →
      ∃ σ : SecAt t.G t.PP.L (spMap φ ≫ χ), SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) =
        SecM.ofSec t.G (h ▸ SecAt.pull t.G t.PP.L θ φK) ∧ NZ t.G t.PP.L (spMap φ ≫ χ) σ := by
    intro V _ _ _ hV φ φK h hc
    obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N _ _ φK _ θ pt _ hT
    obtain ⟨pt₂, hT₂⟩ := thList_cast t.G t.PP.L t.PP.rig m h _ pt₁ _ hT₁
    have hPF : PolFib t.G t.PP.L g (spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
      (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 _) t.PP.isLB t.PP.isLB (SiegLower.isGrpPullback_id _)
        (SiegLower.lbIso_pull_id t.PP.isLB) g (FractionRing R) _).2 _ φK hPol
    have hPF' : PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) := h ▸ hPF
    have hm' : IsUnit (m : V) := by simpa using hm.map φ
    have hcv : ∀ r, φK (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (φ r) :=
      fun r => congrArg (· r) hc
    have hPrim : Prim (algebraMap V (FractionRing V)) (fun a => φK (algebraMap R (FractionRing R) (c a))) := by
      obtain ⟨a, u, hu⟩ := hunit
      refine ⟨fun b => ?_, a, ?_, ?_⟩
      · dsimp only; rw [hcv]; exact RingHom.isIntegralElem_map _
      · dsimp only; rw [← hu]; exact ((u.isUnit.map (algebraMap R (FractionRing R))).map φK).ne_zero
      · dsimp only
        rw [← hu, hcv, show (algebraMap V (FractionRing V) (φ ↑u))⁻¹ = ((algebraMap V (FractionRing V)).comp φ) ↑u⁻¹ from
          (map_units_inv ((algebraMap V (FractionRing V)).comp φ) u).symm, RingHom.comp_apply]
        exact RingHom.isIntegralElem_map _
    exact GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta E H S t g m N V hV (spMap φ ≫ χ) (h ▸ SecAt.pull t.G t.PP.L θ φK) pt₂ _ hodd h3 hm' hPF' hT₂ hPrim
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_of_extends_over_complete_dvrs S t.G t.PP.L t.PP.isLB t.semi R χ θ
    (fun V _ _ _ hV φ φK h hc => (key V hV φ φK h hc).imp fun _ h' => h'.1)
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨p, hps⟩ : ∃ p : PrimeSpectrum R, (p : Sp R) = s := ⟨s, rfl⟩
  have hinjp : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : CharZero (Localization.AtPrime p.asIdeal) := charZero_of_injective_algebraMap hinjp
  obtain ⟨V, _, _, _, φ₀, hV, hinj, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Localization.AtPrime p.asIdeal)
  obtain ⟨φ, hφdef⟩ : ∃ φ : R →+* V, φ = φ₀.comp (algebraMap R (Localization.AtPrime p.asIdeal)) := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef, RingHom.coe_comp]; exact hinj.comp hinjp
  obtain ⟨φK, hc⟩ := exists_fracMap φ hφ
  have h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hc]
  obtain ⟨σV, hσV, z, hz₁, hz₂⟩ := key V hV φ φK h hc
  have hθ : SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R)) = θ := secAt_ext t.G t.PP.L hσ
  have hFl : Flat t.G.hom := by haveI := t.semi.smooth; infer_instance
  have e₁ := pull_pull_cast t.G t.PP.L χ σ φ (algebraMap R (FractionRing R)) (algebraMap V (FractionRing V)) φK h hc
  rw [hθ] at e₁
  have heq : SecAt.pull t.G t.PP.L σ φ = σV :=
    secAt_eq_of_generic t.G t.PP.L _ _ _ (secAt_ext t.G t.PP.L (e₁.trans hσV.symm))
  subst heq
  refine ⟨((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ t.G).left z, ?_,
    mem_nonzeroLocus_of_pullS t.G _ _ σ z hz₂⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Scheme.Hom.comp_apply, hz₁]
  show (spMap φ) (IsLocalRing.closedPoint V) = s
  rw [← hps, hφdef]
  exact spMap_closedPoint p φ₀

end GlobalTheory.UMin.OmExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSectionExtendsNonzeroOfIntegralThetaConstanStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibreSection_extends_nonzero_of_integral_thetaConstants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.UMin.OmExt.om_ext | exact GlobalTheory.UMin.OmExt.om_ext | (intros; apply GlobalTheory.UMin.OmExt.om_ext <;> assumption)
end
end
