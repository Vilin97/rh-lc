module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigenStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaActionStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPtOfCharacter

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineZeroConst

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem line_zero_const {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e

theorem trPt_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] : DegPre.trPt D F (DegPre.zeroF D F) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [DVR.tr_fst, Category.id_comp]
  · refine (DVR.tr_pr D F _).trans ?_
    have : fst (TF (R := R) F) D.P.A ≫ DegPre.zeroF D F = 1 := MonObj.comp_one (M := D.P.A) _
    rw [this, _root_.mul_one, Category.id_comp]

theorem phiRaw_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))), g.b = DegPre.zeroF D F → w.IsGen → ∃ c : Fˣ, ∀ s s' : Raw D F k, PhiRaw D F k 0 g w s s' → (∀ α, (∃ j, (s α).f j ≠ 0) → ∀ z J, Good D.P.L z J → val (g.s α) (𝟙 _) z J = 1) → ∀ α j, (s' α).f j = DegPre.constBF D F c.val _ * (s α).f j := by
  intro R _ _ D F _ _ k g w hb hw
  obtain ⟨b, gs', hg, h0, hm⟩ := g
  dsimp only at hb w
  subst hb
  obtain ⟨c, hc⟩ := line_zero_const D F k w hw
  refine ⟨c, fun s s' H hs α j => ?_⟩
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.phiφ D F 0 α (DegPre.zeroF D F)) (ε' := DegPre.deltaε k)
    (fun U _ h => by
      have e₁ : padd D.P.A (DegPre.cF D F α) (DegPre.zeroF D F) = DegPre.cF D F α :=
        _root_.mul_one (DegPre.cF D F α)
      rw [DegPre.phiφ, trPt_zero, add_zero]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (c := 1) (c' := 1) ?_ ?_)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) rfl
          (DVR.prod_neg _ _ (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) ?_)).symm)
      · simp [Fin.prod_univ_four, DegPre.gtφ, DegPre.gtε, e₁]
      · simp [Fin.prod_univ_two, DegPre.lineφ, DegPre.lineε]
      · simp
      · simp)
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (gs' α) w) (fst (TF (R := R) F) D.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg α) hw) _)
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[D.P.A]))
  have rel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu (corr_of_val D.P.isLB fun y J hJ => by
    rw [val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, z₁]))
  have key : ∀ y J, Good D.P.L y J → sval (s' α) (𝟙 _) y J = sval (s α) (𝟙 _) y J *
      ((val (gs' α) (fst (TF (R := R) F) D.P.A).left y J).val *
        gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val)) := by
    intro y J hJ
    have e := rel _ (𝟙 _) y J hJ
    rw [vu _ _ y J hJ, val_pull hJ, val_mul hJ, Category.id_comp, Category.id_comp, Units.val_mul, hc _ _ y J hJ] at e
    dsimp only at e
    rw [trPt_zero, add_zero] at e
    exact e
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hI' : Good D.P.L y I := hI
  have e₁ := sec_trans (s' α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₂ := sec_trans (s α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (DegPre.constBF D F c.val _ * (s α).f j) =
      gs (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) *
        gs (𝟙 _) y (LB.wchart D.P.L (DegPre.famφ D F α) j) ((s α).f j) :=
    (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y le_top hy _).trans
      (gs_pull (𝟙 _) (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)) rfl)
  rw [Category.id_comp] at e₃
  have e₄ : sval (s α) (𝟙 _) y I * (val (gs' α) (fst (TF (R := R) F) D.P.A).left y I).val = sval (s α) (𝟙 _) y I := by
    by_cases hz : ∃ j, (s α).f j ≠ 0
    · have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (gs' α) (LB.oneGen D.P.L) :=
        corr_of_val D.P.isLB fun z J hJ => (hs α hz z J hJ).trans (val_one _).symm
      rw [val_corr hI' hcorr, val_one, Units.val_one, _root_.mul_one]
    · push_neg at hz
      have : sval (s α) (𝟙 _) y I = 0 :=
        (congrArg (gs (𝟙 _) y _) (hz _)).trans ((gs_eq _ y _ (hI'.mem _ (𝟙 _)) _).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)))
      rw [this, MulZeroClass.zero_mul]
  have e₅ := key y I hI'
  rw [← _root_.mul_assoc, e₄] at e₅
  refine e₁.trans (Eq.trans ?_ (e₃.trans (congrArg _ e₂)).symm)
  refine (congrArg _ e₅).trans ?_
  rw [sval]; ring

end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupThetaStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.product_support_in_subgroup_theta : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  first | exact @GlobalTheory.MulSupp.main | exact GlobalTheory.MulSupp.main | (intros; apply GlobalTheory.MulSupp.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroup

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_mul_pow_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (k l : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (l : ℤ)))) :
    ∃ u : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((k + l : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval u r z J = sval s r z J * sval t r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (φ' := fun _ : Fin 1 => p) (ε' := fun _ => ((k + l : ℕ) : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, zpow_add]) (H1.SectionArithmetic.mulSec s t)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec s t r z hJ)⟩

theorem exists_pow_exp_supp : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U Λ θ f hθ hf l hl
  induction l, hl using Nat.le_induction with
  | base => exact ⟨θ, f, hθ, hf, fun Z r z J _ => (pow_one _).symm⟩
  | succ l hl ih =>
    obtain ⟨σ, g, hσ, hg, hv⟩ := ih
    obtain ⟨u, hu⟩ := exists_mul_pow_sec U.P.L.isLB _ l 1 σ θ
    obtain ⟨g', hg'⟩ := GlobalTheory.BaseExpansionExists.main h₁ h₂ V hV D A G U (l + 1) (Nat.le_add_left 1 l) u
    exact ⟨u, g', hg', GlobalTheory.T.product_support_in_subgroup_theta V hV D A G U Λ l 1 σ θ u g f g' hσ hθ hg' hu hg hf,
      fun Z r z J hJ => by rw [hu Z r z J hJ, hv Z r z J hJ, pow_succ]⟩

end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroupStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaPowers_expansion_support_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  first | exact @GlobalTheory.UU.exists_pow_exp_supp | exact GlobalTheory.UU.exists_pow_exp_supp | (intros; apply GlobalTheory.UU.exists_pow_exp_supp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroup

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PrimeIndex

theorem exists_injective_character (F : Type) [Field F] [IsAlgClosed F] (l : ℕ) (hl : (l : F) ≠ 0) :
    ∃ φ : Multiplicative (ZMod l) →* Fˣ, Function.Injective φ := by
  have : NeZero (l : F) := ⟨hl⟩
  have : NeZero l := NeZero.of_neZero_natCast F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l
  have hu : IsPrimitiveRoot (hζ.isUnit (NeZero.ne l)).unit l := hζ.isUnit_unit (NeZero.ne l)
  exact ⟨(Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).injective⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem sval_pow_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (θ : U.SecGT T 1) (σ : U.SecGT T k)
    (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h₁ : U.PullG F φ 1 θ th) (hk : U.PullG F φ k σ t)
    (hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ k)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (hA : Good A.L z JA) :
    sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t (𝟙 _) z JA =
      sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th
        (𝟙 _) z JA ^ k := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₃ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₃.trans (Category.id_comp _).symm
  have a := h₁ _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG
  have b := (hk _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans ((hp _ h z JG hG).trans (congrArg (· ^ k) a.symm))
  rw [pow_one, mul_pow, ← Units.val_pow_eq_pow_val] at b
  exact (Units.mul_right_inj _).1 b

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem hom_zmod_eq_zero_of_support : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  intro L₁ L₂ V _ _ _ hV D A G _ _ U θ f hθ l hl g hg
  have := hV.1
  have := hV.2.2
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have hl0 : (l : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hl1 : 1 ≤ l := hl.one_le
  obtain ⟨φ, hφ⟩ := exists_injective_character (Kbar V) l hl0
  let χ₀ : Multiplicative D.X →* (Kbar V)ˣ := φ.comp (AddMonoidHom.toMultiplicative g)
  have hχ : ∀ α, χ₀ (Multiplicative.ofAdd α) = φ (Multiplicative.ofAdd (g α)) := fun _ => rfl
  have hχl : χ₀ ^ l = 1 := MonoidHom.ext fun α => by
    show χ₀ (Multiplicative.ofAdd α.toAdd) ^ l = 1
    rw [hχ, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, map_one]
  suffices H : χ₀ = 1 by
    refine AddMonoidHom.ext fun α => ?_
    have e : φ (Multiplicative.ofAdd (g α)) = φ 1 := by rw [← hχ, H, map_one]; rfl
    exact congrArg Multiplicative.toAdd (hφ e)
  obtain ⟨p, pb, pv, pt, pz⟩ := exists_gtPt_of_character V D (Kbar V) χ₀
  obtain ⟨o, -, -, ot, oz⟩ := exists_gtPt_of_character V D (Kbar V) 1
  obtain ⟨m, minj, macts, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action L₁ L₂ V hV D A G U l hl1
  let P : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨p, pt l hχl⟩
  let O : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨o, ot l (one_pow l)⟩
  have ho : o = 0 := (TorusExt.isZero_iff_eq o).1 (oz.2 rfl)
  have mO : m O = 1 := by
    have := madd O O O ((TorusExt.isAdd_iff_eq o o o).2 (by rw [ho, add_zero]))
    exact left_eq_mul.1 this
  suffices H : m P = 1 by
    have e : p = o := congrArg Subtype.val (minj (H.trans mO.symm))
    exact pz.1 (e ▸ oz.2 rfl)
  obtain ⟨σ, fl, hσ, hfl, hpow⟩ := GlobalTheory.T.thetaPowers_expansion_support_subgroup L₁ L₂ V hV D A G U g.ker θ f hθ.1 (fun α hα j => by
    by_contra hj
    exact hα (hg α ⟨j, hj⟩)) l hl1
  obtain ⟨th, hth, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨t, ht, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) l σ
  obtain ⟨s, hs, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) l fl
  obtain ⟨⟨j₀, hj₀⟩, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one L₁ L₂ V hV D A G U θ f hθ th s₀ hth hs₀
  have hts := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) l σ fl t s hσ ht hs
  obtain ⟨ex, ex₁, ex₂, ex₃, -⟩ := GlobalTheory.UU.ExpLinMap.exists_expansion_linear L₁ L₂ V hV D A G U (Kbar V) l hl1
  obtain ⟨hpl, hacts⟩ := macts P
  obtain ⟨ϑ, hϑ⟩ := (GlobalTheory.ThetaIrred.main L₁ L₂ _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl0).1 (m P) hpl
  obtain ⟨w, hw, hΦ⟩ := hacts ϑ hϑ
  obtain ⟨t', ht'⟩ := ThetaScalar.exists_actVal A.isLB ϑ t
  have hact := ht'.isActOf A.isLB
  obtain ⟨c, hc⟩ := GlobalTheory.UU.phiRaw_torus V D (Kbar V) l p w pb hw
  have hs' := hc s _ (hΦ t t' s _ hts (ex₁ (SecMod.mk _ t')) hact) (fun α hα z J hJ => by
    obtain ⟨j, hj⟩ := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) l fl s hs α).1 hα
    have hm : g α = 0 := by
      by_contra h0
      exact hj (hfl α h0 j)
    refine Units.ext ((pv α z J hJ).trans ?_)
    have e₁ : scal (𝟙 (Spec (CommRingCat.of (Kbar V)))) ((1 : (Kbar V)ˣ) : Kbar V) = 1 := by simp [scal]
    rw [hχ, hm, ofAdd_zero, map_one, e₁]
    exact (gs_eq _ z ⊤ trivial _).trans ((congrArg _ (map_one _)).trans (map_one _)))
  have e : SecMod.mk _ t' = c.val • (SecMod.mk _ t : EA A (jFK (R := V) (Kbar V)) l) := by
    refine sub_eq_zero.1 (ex₃ _ fun α => ?_)
    rw [map_sub, map_smul, sub_eq_zero]
    refine DVR.SecOps.sec_ext fun j => (hs' α j).trans ?_
    rw [ex₂ t s hts α]
    rfl
  refine hϑ.symm.trans (GlobalTheory.T.thetaOperator_point_zero_of_power_eigen _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl1 (SecMod.mk _ th) (SecMod.mk _ t) ϑ c
    (fun h0 => hj₀ ((SecMod.eq_zero_iff_coord _).1 h0 j₀))
    (fun z J hJ => sval_pow_of_pullG U (Kbar V) (toUnit _) l θ σ th t hth ht hpow z J hJ) ?_)
  rw [← e]
  exact hact

end GlobalTheory.UU.PrimeIndex
end
end
end
