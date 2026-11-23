module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparatesStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPointStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ s : J → Fam u.D.toPre (PadicAlgCl p) k, (∀ i, FamOf u.D.toPre _ (f i) (s i)) → ∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), u.GtN g ν → w.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ α, (∀ i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m) ∧ (∀ i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α))) ∧ ∃ i, ‖GlobalTheory.UT.coef (s i) g w α‖ = κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := by
  first | exact @GlobalTheory.TermSize.term_sizes | exact GlobalTheory.TermSize.term_sizes | (intros; apply GlobalTheory.TermSize.term_sizes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZeroStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  first | exact @GlobalTheory.GtDescent.exists_integral_point | exact GlobalTheory.GtDescent.exists_integral_point | (intros; apply GlobalTheory.GtDescent.exists_integral_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SeriesProportionalAddIotaIff

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IotaShift
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (y : D.X) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen)
    (b : TF (R := R) F ⟶ D.P.A) (hb : b = g.b * cP D _ y) :
    ∃ ω : Frm D F k b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J =
      val w (𝟙 _) z J * val (g.s y) (𝟙 _) z J ^ k *
        (val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J *
          val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J) := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : jFK (R := R) F ≫ D.xK y = (cP D (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      have a₃ : ∏ i, h (DegPre.gtφ D F g.b y i) ^ ((k : ℤ) * DegPre.gtε i) =
          (∏ i, h (DegPre.gtφ D F g.b y i) ^ DegPre.gtε i) ^ (k : ℤ) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [a₃, prod_gt, prod_line, prod_line, hb, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (GeneratorPullback.powGen D.P.L _ _ (g.s y) k))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (powGen_isGen _ _ _ _ (g.isGen y) k))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen y) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _))
  refine ⟨u, hu, fun z J hJ => ?_⟩
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (map_pow _ _ _))) ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _))))

theorem coef_shift_frame (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) :
    ∃ ω : Frm D F k g'.b, ω.IsGen ∧ ∀ (s : Fam D F k) α, coef s g w (α + k • y) = coef s g' ω α := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  rw [ιb] at hb
  obtain ⟨ω, hω, vω⟩ := exists_frame y g w hw g'.b hb
  refine ⟨ω, hω, fun s α => coef_eq fun z J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k y α
  have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _
    (lift (𝟙 (TF (R := R) F)) g.b).left z J hJ
  have t : lift (𝟙 (TF (R := R) F)) g.b ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) g'.b := by
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
  rw [hv u hu hc _ _ z J hJ, ← Over.comp_left, t, val_famMult _ hJ, uVal, lift_fst_assoc, lift_fst, lift_snd,
    Category.id_comp, Over.id_left] at e₁
  have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g α y k
  rw [Category.id_comp, Over.id_left] at e₂
  have e₃ := hs α z J hJ
  have e₄ : th D z J (cP D _ α) g.b h.b = th D z J (cP D _ α) g.b (cP D _ y) := by rw [ιb]
  have e₅ : val (h.s α) (𝟙 _) z J = val (D.tau y α) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J := ιv α z J hJ
  rw [e₅, e₄] at e₃
  rw [isCoef_coef g' hω α s z J hJ, e₁, vω z J hJ]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
  linear_combination (norm := module) a₃ - a₂

theorem coef_shift (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) (w' : Frm D F k g'.b) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (s : Fam D F k) α, coef s g' w' α = c * coef s g w (α + k • y) := by
  obtain ⟨ω, hω, e⟩ := coef_shift_frame hG hι hadd w hw
  obtain ⟨c, hc, -, e'⟩ := ((coef_basic R D F k g').2.2 ω hω).2.2.1 w' hw'
  exact ⟨c, hc, fun s α => by rw [e', e]⟩

end

theorem parAt_add_iota : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k a g h g' y _ hι hadd
  constructor
  · intro H w' hw' l hl
    obtain ⟨w, hw⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g).1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w hw l hl
    refine ⟨c * κ, mul_ne_zero hc hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc, funext (e s)]
    exact ((Equiv.addRight (k • y)).hasSum_iff.2 (hs σ s hσ)).mul_left c
  · intro H w hw l hl
    obtain ⟨w', hw'⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g').1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w' hw' l hl
    refine ⟨c⁻¹ * κ, mul_ne_zero (inv_ne_zero hc) hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc]
    refine (Equiv.addRight (k • y)).hasSum_iff.1 ?_
    have := (hs σ s hσ).mul_left c⁻¹
    simp only [e s, inv_mul_cancel_left₀ hc] at this
    exact this

end GlobalTheory.ZH.IotaShift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SeriesProportionalAddIotaIffStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.seriesProportional_add_iota_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  first | exact @GlobalTheory.ZH.IotaShift.parAt_add_iota | exact GlobalTheory.ZH.IotaShift.parAt_add_iota | (intros; apply GlobalTheory.ZH.IotaShift.parAt_add_iota <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPointsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.valuations_torusExtension_points : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  first | exact @GlobalTheory.ZH.TorusVal.main | exact GlobalTheory.ZH.TorusVal.main | (intros; apply GlobalTheory.ZH.TorusVal.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesAtPointIntegralOfPeriodValuation

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesAtPoint

section Pull
variable {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secLin_of_secScal {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem exists_pull (hL : L.IsLB) {φ : K₁ → (Y ⟶ X)} {ε : K₁ → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ' : K₁ → (Y' ⟶ X)} (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s' φ ε s h 1 ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y') (j : K₁ → L.ι), ⊤ ≤ (x ≫ h) ⁻¹ᵁ LB.wchart L φ j →
        valR x (LB.wchart L φ' j) (s'.f j) = valR (x ≫ h) (LB.wchart L φ j) (s.f j) := by
  subst e
  refine ⟨DVR.pullSec L φ ε s h, DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ (𝟙 _) y hJ).symm, fun R _ x j hj => ?_⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  refine (CrdCalc.valR_res x _ hj' _).trans ?_
  exact (CrdCalc.valR_eq x (h ⁻¹ᵁ LB.wchart L φ j) hj _).trans (CrdCalc.valR_eq (x ≫ h) _ hj (s.f j)).symm

theorem exists_isGen {R : Type} [CommRing R] [IsLocalRing R] {M : LB (Sp R)} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  have : (𝟙 (Sp R) : Sp R ⟶ Sp R) (IsLocalRing.closedPoint R) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  have hl' : ⊤ ≤ M.U l := (CrdCalc.top_le_iff (𝟙 (Sp R)) _).2 hl
  have le : ∀ V : (Sp R).Opens, V ≤ V ⊓ M.U l := fun V => le_inf le_rfl (le_top.trans hl')
  refine ⟨⟨fun j => res (le _) (M.g j l)⟩, fun i j => ?_⟩
  have e := congrArg (res (le (M.U i ⊓ M.U j))) (hM.cocycle i j l)
  rw [map_mul, DVR.res_res', DVR.res_res', DVR.res_res', DVR.res_refl'] at e
  simp only [DVR.res_res']
  exact e.symm

end Pull

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_frm (k : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) :
    ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen :=
  exists_isGen (R := PadicAlgCl p) (DVR.linComb_isLB _ u.D.toPre.P.isLB _ _)

theorem hasSum_crd {k : ℕ} {J : Type} {σ : J → (u.H k).Sec} {f : J → ∀ α, u.D.toPre.SecB k α}
    (hf : ∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) {s : J → Fam u.D.toPre (PadicAlgCl p) k}
    (hs : ∀ i, FamOf u.D.toPre _ (f i) (s i)) {a : u.PtC} {g : GtPtF u.D.toPre (PadicAlgCl p)} (hg : u.ParAt k a g)
    {w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b} (hw : w.IsGen) {v : J → PadicAlgCl p}
    (hv : Crd (u.H k) σ (u.toG a) v) :
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ i, HasSum (fun χ => GlobalTheory.UT.coef (s i) g w χ) (κ * v i) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  obtain ⟨l, rfl⟩ : ∃ l₀, l = fun _ : Fin 1 => l₀ := ⟨l 0, funext fun i => congrArg l (Subsingleton.elim _ _)⟩
  obtain ⟨κ, hκ, H⟩ := hg w hw l (hl.trans ((u.toG a).preimage_mono
    (LB.wchart_le u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l) 0)))
  refine ⟨κ * (c⁻¹).val, mul_ne_zero hκ (Units.ne_zero _), fun i => ?_⟩
  obtain ⟨σ', h₁, h₂⟩ := exists_pull u.U.LG.isLB (σ i) (UnifPre.gFK (G := u.G) (PadicAlgCl p))
    (φ' := fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (funext fun _ => (Category.comp_id _).symm)
  have e : (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd]
    rfl
  have hsum := H σ' (s i) ⟨1, fun _ => 1, fun _ => σ i, fun _ => f i, fun _ => hf i, secLin_of_secScal _ h₁,
    fun α => secLin_of_secScal _ (hs i α)⟩
  have h₃ := h₂ (PadicAlgCl p) (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left (fun _ => l) (e.symm ▸ hl)
  have h₄ := h₃.trans (congrArg (fun x => valR x (LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l))
    ((σ i).f fun _ => l)) e)
  rw [hv, _root_.mul_assoc, Units.inv_mul_cancel_left]
  exact (congrArg (fun x => HasSum _ (κ * x)) h₄).mp hsum

theorem main : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB a ha w hw
  have hN : 4 ≤ S.N := (GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ u).2.2.2.1
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) hN
  obtain ⟨-, hsep, hon⟩ := GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB
  obtain ⟨a, rfl⟩ := hon a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_torusExtension_parameter_genericFibrePoint hL hT o Ω S ρ p y₀ u l a
  obtain ⟨-, hex, huq, hadd, hι⟩ := GlobalTheory.T.valuations_torusExtension_points hL o Ω S ρ p y₀ u l
  obtain ⟨ν, hν⟩ := hex g
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) S.N, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hB.2.2.2.2.1 i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D S.N s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  obtain ⟨fr, hfr⟩ := exists_frm u S.N g
  obtain ⟨κ, hκ, hsum⟩ := hasSum_crd u hB.2.2.2.1 hs hg hfr hw
  refine ⟨ν, ?_, ?_⟩
  · obtain ⟨r, hr, H⟩ := GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB s hs g ν fr hν hfr
    refine ⟨fun α i => κ⁻¹ * GlobalTheory.UT.coef (s i) g fr α, ‖κ⁻¹‖ * r,
      mul_pos (norm_pos_iff.2 (inv_ne_zero hκ)) hr, fun i => ?_, fun α i h => ?_, fun α => ⟨fun i => ?_, ?_⟩⟩
    · have := (hsum i).mul_left κ⁻¹
      rwa [inv_mul_cancel_left₀ hκ] at this
    · exact (H α).1 i (right_ne_zero_of_mul h)
    · rw [norm_mul, _root_.mul_assoc]
      exact mul_le_mul_of_nonneg_left ((H α).2.1 i) (norm_nonneg _)
    · obtain ⟨i, hi⟩ := (H α).2.2
      exact ⟨i, by rw [norm_mul, _root_.mul_assoc, hi]⟩
  · rintro ⟨m, hm⟩
    obtain ⟨-, hio, hsub⟩ := GlobalTheory.ZH.gt_add_iota_sub_exist hL o Ω S ρ p y₀ u
    obtain ⟨h, hh⟩ := hio m
    obtain ⟨g', hg'⟩ := hsub g h
    obtain ⟨ν', hν'⟩ := hex g'
    have e := huq g _ _ hν (hadd g' h g _ _ hg' hν' (hι m h hh))
    have e0 : (ν' : u.D.toPre.X → ℝ) = 0 := funext fun α => by
      have := congrFun e α
      rw [Pi.add_apply, hm α] at this
      exact right_eq_add.1 this
    obtain ⟨c, hc, hlev⟩ := GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero hL o Ω S ρ p y₀ u g' (e0 ▸ hν')
    obtain ⟨a', ha'⟩ := hon (gPt p ≫ c) (by rw [Category.assoc, hc])
    have hp' : u.ParAt S.N a' g :=
      (GlobalTheory.T.seriesProportional_add_iota_iff hL o Ω S ρ p y₀ u S.N a' g' h g m hN1 hh hg').1
        ((GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g' a' hc ha'.symm hlev).2 S.N hN1)
    obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (DVR.linComb_isLB _ u.U.LG.isLB _ _) σ (u.toG a')
    obtain ⟨κ', hκ', hsum'⟩ := hasSum_crd u hB.2.2.2.1 hs hp' hfr hw'
    have h₁ := CrdCalc.crd_smul (Units.mk0 κ hκ) hw
    have h₂ := CrdCalc.crd_smul (Units.mk0 κ' hκ') hw'
    have e₃ : (fun j => ((Units.mk0 κ' hκ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w' j) =
        fun j => ((Units.mk0 κ hκ : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w j :=
      funext fun j => (hsum' j).unique (hsum j)
    rw [e₃] at h₂
    exact ⟨c, hc, ha'.symm.trans (congrArg u.toG (hsep a' a _ h₂ h₁))⟩

end GlobalTheory.ZH.SeriesAtPoint
end
end
