module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  intro k Ω _ _ _ _ M hn V z hz
  obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) hz
  have hWV' : W ≤ V := hWV
  have hne : ((W : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzW⟩
  refine ⟨W, hW, hzW, hWV', ?_, ?_⟩
  · have h1 : (M.s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType M.s M.lft ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    have h4 := h1.comp h2
    letI := ((M.s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
    haveI : Algebra.FiniteType k Γ(M.Z, W) := h4
    haveI : IsNoetherianRing Γ(M.Z, W) := Algebra.FiniteType.isNoetherianRing k _
    exact isNoetherianRing_of_ringEquiv _ (M.sectionsEquiv W hne)
  · haveI := GlobalTheory.ZH.RatModel.isFractionRing_ringOn hW hne
    refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ?_
    have hmem : x ∈ M.ringOn W := GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z' hz' => by
      haveI := GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hn z'
      have hle := GlobalTheory.ZH.RatModel.ringOn_le_O (M := M) hz'
      letI : Algebra (M.ringOn W) (M.O z') := (Subalgebra.inclusion hle).toRingHom.toAlgebra
      haveI : IsScalarTower (M.ringOn W) (M.O z') Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral (M.O z') x := hx.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    exact ⟨⟨x, hmem⟩, rfl⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | exact GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | (intros; apply GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.AffChart

open GlobalTheory.Points

theorem exists_openImm_spec_ringOn (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω)
    (W : M.Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty) :
    ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧
      spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  let φ : Γ(M.Z, W) ⟶ CommRingCat.of (M.ringOn W) := (M.sectionsEquiv W hne).toCommRingCatIso.hom
  haveI : IsIso φ := inferInstanceAs (IsIso (M.sectionsEquiv W hne).toCommRingCatIso.hom)
  refine ⟨Spec.map φ ≫ hW.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, hW.opensRange_fromSpec]
  · have hp := M.top_le_preimage_pt hne
    have e : φ ≫ CommRingCat.ofHom (algebraMap (M.ringOn W) Ω) = valMap M.pt W hp := by
      ext f
      exact (M.coe_sectionsEquiv W hne f).trans (M.res_apply W hne f).symm
    rw [spMap, ← Category.assoc, ← Spec.map_comp, e, specMap_valMap_fromSpec]

end GlobalTheory.Div.AffChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_openImmersion_spec_ringOn_affine : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (W : M.Z.Opens), IsAffineOpen W → (W : Set M.Z).Nonempty → ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧ spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  first | exact @GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | exact GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | (intros; apply GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ChartDiv

theorem chart_ratio_mem_O : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  intro k Ω _ _ _ M n c h a z hc hz
  have hx : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ chart k n a := M.top_le_preimage_pt (U := h ⁻¹ᵁ chart k n a) ⟨z, hz⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c a hc hx
  refine ⟨ha, fun z' hz' b => ?_⟩
  rw [← hb b, Points.valR_comp, ← Points.valF_eq_valR]
  exact RatModel.valF_mem_O hz' _

end GlobalTheory.UMin.ChartDiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  first | exact @GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | exact GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | (intros; apply GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem exists_locSec_of_openImmersion (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (ξ : Sp K ⟶ S)
    (e : spMap (algebraMap R K) ≫ χ = ξ) (θ : SecAt t.G t.PP.L ξ) (pt : Fin N → (Over.mk ξ ⟶ t.G)) (c : Fin N → R)
    (hodd : Odd m) (hm3 : 3 ≤ m) (hm : IsUnit (m : R)) (hpol : PolFib t.G t.PP.L g ξ)
    (hth : ThList t.G t.PP.L t.PP.rig m ξ θ pt (fun a => algebraMap R K (c a))) (hu : ∃ a, IsUnit (c a)) :
    ∃ s : LocSec t.G t.PP.L χ.opensRange, IsLocSec s ∧ GenIs ξ s (SecM.ofSec t.G θ) ∧ FibNz s χ.opensRange := by
  subst e
  have hlft : LocallyOfFiniteType t.G.hom := by
    haveI := t.semi.smooth
    infer_instance
  obtain ⟨σ, hσ, hσnz⟩ := GlobalTheory.T.extend_regularThetaSection_any_fractionField E H S t g m N R K χ θ pt c hodd hm3 hm hpol hth hu
  obtain ⟨s, hs, hsgen, hsfib⟩ := GlobalTheory.T.exists_localSection_of_openImmersion_spec S t.G t.PP.L R χ σ hlft hσnz
  refine ⟨s, hs, ?_, hsfib⟩
  have := hsgen K (algebraMap R K)
  rw [hσ] at this
  exact this

theorem exists_locSec_theta_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h θ pt hN hodd hm3 hmu hpol hgen hth hcrd a z hz
  obtain ⟨hca, hdiv⟩ := GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring k Ω M n c h a z hcrd hz
  obtain ⟨W, hWa, hzW, hWV, hnoeth, hic⟩ := GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed k Ω M hN (h ⁻¹ᵁ chart k n a) z hz
  have hne : (W : Set M.Z).Nonempty := ⟨z, hzW⟩
  obtain ⟨χ, hoi, hrange, hgenpt⟩ := GlobalTheory.T.exists_openImmersion_spec_ringOn_affine k Ω M W hWa hne
  haveI := M.isFractionRing_ringOn hWa hne
  let c'' : Fin (n + 1) → M.ringOn W := fun b =>
    ⟨c b / c a, RatModel.mem_ringOn.2 fun z' hz' => hdiv z' (hWV hz') b⟩
  let θ' : SecAt t.G t.PP.L M.pt :=
    SecM.toSec t.G ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)
  have hmΩ : (m : Ω) ≠ 0 := by
    have := hmu.map (algebraMap k Ω)
    rw [map_natCast] at this
    exact this.ne_zero
  have hth' : ThList t.G t.PP.L t.PP.rig m M.pt θ' pt (fun b => algebraMap (M.ringOn W) Ω (c'' b)) := by
    refine ⟨hth.1, fun b => ?_, hth.2.2⟩
    have key := GlobalTheory.UMin.thG_smul_iff M.Z t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m Ω M.pt θ θ' (pt b)
      (c a)⁻¹ (c b) (c b / c a) hodd hmΩ hpol rfl (hth.2.1 b)
    exact key.2 (by rw [div_eq_inv_mul])
  have hmR : IsUnit (m : M.ringOn W) := by
    have := hmu.map (algebraMap k (M.ringOn W))
    rwa [map_natCast] at this
  have hunit : ∃ b, IsUnit (c'' b) := ⟨a, by
    have : c'' a = 1 := Subtype.ext (by simp [c'', div_self hca])
    rw [this]; exact isUnit_one⟩
  obtain ⟨s, hs, hsgen, hsfib⟩ := exists_locSec_of_openImmersion E H M.Z t g m (n + 1) (M.ringOn W) Ω χ M.pt hgenpt θ' pt c'' hodd hm3 hmR hpol hth' hunit
  exact ⟨χ.opensRange, by rw [hrange]; exact hzW, by rw [hrange]; exact hWV, s, hs, hsgen, hsfib⟩

end GlobalTheory.UMin.ThBdl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localSection_thetaQuotient_projChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  first | exact @GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | exact GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | (intros; apply GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart <;> assumption)
end
end
