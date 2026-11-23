module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFormalSectionCoefficientFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoGermTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamily
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOnOfTExpGen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumMult

theorem chartExpOn_of_tExp_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (e : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G) (n : ℕ)
    (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U b n 0) (hF : Small I (w := id) F)
    (hf : ∀ β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f β) x z J = sval (F β) x z J)
    (hτ : TExp U τ (w := id) F) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W))
    (hg : ∀ (z : (thickObj R I e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG I e G).left) = i' 0 →
      gs (𝟙 _) z W g = sval τ (𝟙 _) z J') : ChartExpOn U e n i' W g f := by
  classical
  let S : Finset D.toPre.X := (hF e).toFinset
  have hS : ∀ α ∉ S, Van I (F α) e := fun α hα => by_contra fun h => hα ((hF e).mem_toFinset.2 h)
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    have h0 : sval (f α) (DVR.pGl U e) y J = 0 := (hf α _ _ y J hJ).trans (hS α hα _ (U.gt e).q.left y J hJ)
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ h0).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ jf jt hj hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy.1) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy.1) a.2])
    obtain ⟨J', hJ', eJ'⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit.{1}) (fun _ => 𝟙 _ ≫ (fstG I e G).left)
      (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl) (fun _ => mem_pull.1 hy.1.1.1.2)
    have e₀ : J (𝟙 _ ≫ (U.gt e).pG.left) = p₁ PUnit.unit := by rw [Category.id_comp]; exact eJ (.inl PUnit.unit)
    have e₁ : J' (𝟙 _ ≫ (fstG I e G).left) = p₂ PUnit.unit := eJ' PUnit.unit
    have H := hτ S hS _ (𝟙 _) y J J' hJ hJ'
    rw [evalE, zpow_zero, _root_.mul_one, zpow_natCast, e₀, e₁] at H
    refine ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y inf_le_right hy g).trans
      (hg y J' hy.2 hJ' (e₁.trans hj.symm))))).trans
      (H.trans (Eq.symm ?_))
    · rw [← Units.val_pow_eq_pow_val, gs_unit (𝟙 _) y _ hy, map_pow]
      exact congrArg (fun u => (u ^ n).val) (gm_res (𝟙 _) y _ hy _)
    · refine (DVR.gs_fsum (𝟙 _) y _ hy _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
      have l₁ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expW_le_f e (p₁, p₂) i' jf jt α.2)
      have l₂ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expWeight_le_chart_weight e (p₁, p₂) i' jf jt α.2)
      have a₁ := (gs_res (𝟙 _) y l₁ hy (((DVR.pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
        (gs_pull (𝟙 _) (DVR.pGl U e) y (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hy) ((f α.1).f (jf α.1)))
      have a₂ := (gs_unit (𝟙 _) y _ hy (res l₂ ((DVR.tG U e α.1).s (jt α.1)))).trans
        (congrArg Units.val (gm_res (𝟙 _) y l₂ hy _))
      have b₁ := sval_of (f α.1) (𝟙 _ ≫ DVR.pGl U e) y J (jf α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inl (α, a))))
      have b₂ := val_of (DVR.tG U e α.1) (𝟙 _) y J (jt α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (α, a))))
      exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (a₁.trans (b₁.symm.trans (hf α.1 _ _ y J hJ)))
        (a₂.trans (congrArg Units.val b₂.symm)))

theorem chartExpOn_of_tExp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U.toUnifPre b n 0), Small (maximalIdeal R) (w := id) F → (∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f β) x z J = sval (F β) x z J)) → TExp U.toUnifPre τ (w := id) F → ∀ (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R (maximalIdeal R) e G).left.Opens) (g : Γ((thickObj R (maximalIdeal R) e G).left, W)), (∀ (z : (thickObj R (maximalIdeal R) e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG (maximalIdeal R) e G).left) = i' 0 → gs (𝟙 _) z W g = sval τ (𝟙 _) z J') → GlobalTheory.MumMult.ChartExpOn U.toUnifPre e n i' W g f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U e b n F f τ hF hf hτ i' W g hg =>
    chartExpOn_of_tExp_gen U.toUnifPre e b n F f τ hF hf hτ i' W g hg

end GlobalTheory.MumMult
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFam

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwBack

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tw (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n : ℕ) (β : D.X) {U : Type} [CommGroup U]
    (g : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, g (tφ D a β k) ^ tε n 0 k = ∏ k, g (D.famφB β k) ^ DegPre.famε n k := by
  rw [Fin.prod_univ_castSucc (n := 4)]
  show (∏ k : Fin 4, _) * g a.left ^ (0 : ℤ) = _
  rw [zpow_zero, _root_.mul_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  fin_cases k <;> rfl

theorem vanMod_of_van (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) (h : Van I b e) :
    VanMod I b e := by
  intro j
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (thickObj R I e D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero _ y _ hy).symm)
  refine (sec_trans b _ y hy (Good.mem hJ (D.famφB α) _)).trans ?_
  exact (congrArg _ (h _ (𝟙 _) y J hJ)).trans (mul_zero _)

theorem shift_zero {X : Type} [AddCommGroup X] (h h' : X →+ X) (n : ℕ) (mu : X) :
    shift h h' n 0 mu = n • mu := by
  rw [shift, zero_smul, add_zero, natCast_zsmul]

theorem famFE_of_tfe (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (n : ℕ) (F : ∀ β, SecT D a n 0 β)
    (hF : TFE h h' F)
    (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε n)))
    (hs : ∀ α (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) x z J = sval (F α) (x ≫ (DegPre.prB D (FractionRing R)).left) z J) :
    DegPre.FamFE D (FractionRing R) n s := by
  intro mu α u hu hc
  have hT : TRel h mu (F α) (F (α + n • mu)) := by
    have := hF mu α
    rwa [shift_zero] at this
  obtain ⟨u', hu', hv⟩ := exists_gen D.P.isLB (φ' := dφ D a mu α (α + n • mu)) (ε' := dε n 0) (fun U _ g => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, dφ, dε, zpow_neg,
      Finset.prod_inv_distrib, DVR.GC.famφ_eq]
    rw [prod_tw D a n _ (fun ψ => g ((DegPre.prB D (FractionRing R)).left ≫ ψ)),
      prod_tw D a n _ (fun ψ => g ((DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ ψ))])
    u hu
  have hfac : IsFac D a h n 0 mu α (α + n • mu) u' := by
    refine ⟨hu', fun z J hJ => ?_⟩
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp, DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, Category.id_comp] at e
    rw [hv _ _ z J hJ, zpow_zero, _root_.mul_one, add_zero, zpow_natCast, zpow_natCast]
    exact e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (map_pow _ _ _) rfl) (map_pow _ _ _))
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, ← hv _ _ y J hJ, Category.assoc]
  exact hT u' hfac _ (𝟙 _) y J hJ

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h h' : D.toPre.X →+ D.toPre.X) (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β), Small (maximalIdeal R) (w := id) F → TFE h h' F → ∃ Φ : IntFam (maximalIdeal R) D.toPre n, ∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (Φ.f β) x z J = sval (F β) x z J) := by
  intro R _ _ _ _ D a h h' n F hS hF
  have hL := D.toPre.P.isLB
  choose f hf using fun β => exists_sec hL (φ' := D.toPre.famφB β) (ε' := DegPre.famε n)
    (fun U _ g => prod_tw D.toPre a n β g) (F β)
  choose s hs using fun β => exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) β) (ε' := DegPre.famε n)
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
    (DVR.pullSec D.toPre.P.L _ _ (f β) (DegPre.prB D.toPre (FractionRing R)).left)
  have hs' : ∀ β (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J),
      Good D.toPre.P.L z J → sval (s β) x z J = sval (f β) (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J :=
    fun β Z x z J hJ => (hs β Z x z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ x z hJ)
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold Out.scal; rw [map_one, map_one]
  refine ⟨⟨⟨s, famFE_of_tfe D.toPre a h h' n F hF s fun β Z x z J hJ => (hs' β Z x z J hJ).trans (hf β Z _ z J hJ)⟩,
    f, fun β => ?_, fun e => (hS e).subset fun β hβ hv => hβ (vanMod_of_van _ _ e fun Z x z J hJ =>
      (hf β Z _ z J hJ).trans (hv Z x z J hJ))⟩, hf⟩
  rw [h1]
  exact DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' β _ _ y J hJ).symm

end GlobalTheory.TwBack
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFormalSectionCoefficientFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_mumford_formal_section_coefficient_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ g : ∀ β, SecT D.toPre a N (-1) β, Small (maximalIdeal R) (w := id) g ∧ TFE h h' g ∧ (∀ β, β ≠ 0 → Van (maximalIdeal R) (g β) 0) ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval (g 0) (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J = sval σ₀ (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J := by
  first | exact @GlobalTheory.MumCoef.coef | exact GlobalTheory.MumCoef.coef | (intros; apply GlobalTheory.MumCoef.coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  first | exact @GlobalTheory.TwFam.exists_pull_expansion | exact GlobalTheory.TwFam.exists_pull_expansion | (intros; apply GlobalTheory.TwFam.exists_pull_expansion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.multiplier_power_mul_pullback_small_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.ZmPow.pow_mul_small | exact GlobalTheory.ZmPow.pow_mul_small | (intros; apply GlobalTheory.ZmPow.pow_mul_small <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumMult

theorem gs_pow_mul_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (v u : Y ⟶ X) (N k : ℕ)
    (τ : LB.Sec (LB.LinComb L (K := Fin 2) ![v, u] ![(N : ℤ), -1])) (s : H0 L k) (i i' : Fin 1 → L.ι)
    (hle : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ LB.wchart L ![v, u] ![i' 0, i 0])
    (z : Y) (J' : (Y ⟶ X) → L.ι) (hz : z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i') (hJ : Good L z J')
    (hv : J' (𝟙 Y ≫ v) = i' 0) :
    gs (𝟙 Y) z (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
      ((Y.presheaf.map (homOfLE hle).op).hom (τ.f ![i' 0, i 0]) ^ k *
        (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i)).op).hom ((u.app (secChart L i)).hom (s.f i))) =
      sval τ (𝟙 Y) z J' ^ k * sval s (𝟙 Y ≫ u) z J' := by
  have hm : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L ![v, u] ![i' 0, i 0] := hle hz
  have hu : (𝟙 Y ≫ u) z ∈ secChart L i := hz.1
  have hv' : (𝟙 Y ≫ v) z ∈ L.U (i' 0) := Set.mem_iInter.1 hz.2 0
  have a0 : ∀ x y : Γ(Y, u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i'),
      gs (𝟙 Y) z _ (x ^ k * y) = gs (𝟙 Y) z _ x ^ k * gs (𝟙 Y) z _ y := fun x y => by
    rw [gs_eq _ _ _ hz, gs_eq _ _ _ hz, gs_eq _ _ _ hz, map_mul, map_mul, map_pow, map_pow]
  have a1 := gs_res (𝟙 Y) z hle hz (τ.f ![i' 0, i 0])
  have a2 := (gs_res (𝟙 Y) z (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i) hz ((u.app (secChart L i)).hom (s.f i))).trans (gs_pull (𝟙 Y) u z _ hu (s.f i))
  rw [a0, a1, a2, sec_trans τ (𝟙 Y) z hm (hJ.mem _ (𝟙 Y)), sec_trans s (𝟙 Y ≫ u) z hu (hJ.mem _ _)]
  have e1 : trF (L := L) ![v, u] ![(N : ℤ), -1] (𝟙 Y) z ![i' 0, i 0] (fun k => J' (𝟙 Y ≫ (![v, u] : Fin 2 → _) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    change gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U (J' (𝟙 Y ≫ v))) (L.g (i' 0) (J' (𝟙 Y ≫ v))) ^ (N : ℤ) *
      gm (𝟙 Y ≫ u) z (L.U (i 0) ⊓ L.U (J' (𝟙 Y ≫ u))) (L.g (i 0) (J' (𝟙 Y ≫ u))) ^ (-1 : ℤ) = _
    have gself : ∀ c : L.ι, c = i' 0 → gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U c) (L.g (i' 0) c) = 1 := by
      rintro c rfl; exact gm_self hL _ _ hv'
    rw [gself _ hv, one_zpow, _root_.one_mul, zpow_neg, zpow_one]
  have e2 : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (𝟙 Y ≫ u) z i
      (fun k => J' ((𝟙 Y ≫ u) ≫ (fun _ : Fin 1 => 𝟙 X) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u)))) ^ k := by
    simp only [trF, Fin.prod_univ_one]
    have gid : ∀ f : Y ⟶ X, f = 𝟙 Y ≫ u →
        gm f z (L.U (i 0) ⊓ L.U (J' f)) (L.g (i 0) (J' f)) = gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) := by
      rintro f rfl; rfl
    rw [gid _ (Category.comp_id _), zpow_natCast]
  rw [e1, e2]
  unfold sval
  generalize gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) = A
  have hA : ((A⁻¹ : _ˣ) : Y.presheaf.stalk z) ^ k * ((A ^ k : _ˣ) : Y.presheaf.stalk z) = 1 := by
    rw [Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  rw [mul_pow, _root_.mul_mul_mul_comm, hA, _root_.one_mul]

private theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Y.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_mult_of_posN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb N hN hP σ₀ x hx hnz
  obtain ⟨g, gsm, gtfe, gvan, g0⟩ := GlobalTheory.T.exists_mumford_formal_section_coefficient_family R hR.1 D a a' h h' hE N hN hP σ₀
  choose τ hτ using fun e => GlobalTheory.TwFamGlue.glue R hR.1 D a A G hG U e (b e) (hb.2.2.1 e) (N : ℤ) (-1) D.toPre.X id g gsm
  have hle : ∀ e (i i' : Fin 1 → U.LG.L.ι), multW U b e i i' ≤ LB.wchart U.LG.L
      ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![i' 0, i 0] := by
    intro e i i' y hy
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · simpa using Set.mem_iInter.1 hy.2 0
    · simpa using Set.mem_iInter.1 hy.1 0
  refine ⟨fun e i i' => ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hle e i i')).op).hom
    ((τ e).f ![i' 0, i 0]), ?_, ?_⟩
  · intro k hk f s hs
    obtain ⟨ρ, ρsm, ρtfe, hρ⟩ := GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism R hR.1 D a a' h h' hE A G hG U b hb k s f hs
    obtain ⟨F, Fsm, Ftfe, hF⟩ := GlobalTheory.T.multiplier_power_mul_pullback_small_family R hR.1 D a a' h h' hE A G hG U b hb N k g ρ gsm ρsm gtfe ρtfe
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.TwBack.exists_intFam R hR.1 D a h h' (N * k) F Fsm Ftfe
    refine ⟨Φ, fun e i i' => ?_⟩
    obtain ⟨τ', hτ'1, hτ'2⟩ := hρ e
    obtain ⟨τ'', h1, h2⟩ := hF e (τ e) τ' (hτ e) hτ'2
    refine GlobalTheory.MumMult.chartExpOn_of_tExp R hR.1 D a A G hG U e (b e) (N * k) F Φ.f τ'' Fsm hΦ h2 i' _ _ ?_
    intro z J' hz hJ' hv
    rw [h1 _ _ z J' hJ', hτ'1 _ _ z J' hJ']
    exact gs_pow_mul_pull U.LG.isLB _ _ N k (τ e) s i i' (hle e i i') z J' hz hJ' hv
  · refine ⟨x, hx, fun y hy i i' hyW => ?_⟩
    choose J hJ using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (χ y)
    choose J' hJ' using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left => exists_chart U.LG.isLB (χ y)
    have hx0 : IsUnit (sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J) := by
      have hm := Good.mem (L := D.toPre.P.L) hJ
        (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (𝟙 _ ≫ (U.gt 0).pG.left)
      have hyx : (𝟙 _ ≫ (U.gt 0).pG.left : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) y = x := hy
      refine (isUnit_gs_iff_mem _ y _ hm _).2 ?_
      rw [hyx] at hm ⊢
      exact hnz _ hm
    have hg0 : sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J = sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J :=
      g0 _ (𝟙 _ ≫ (U.gt 0).q.left) y J hJ
    have hexp := hτ 0 {0} (fun β hβ => gvan β (by simpa using hβ)) _ (𝟙 _) y J J' hJ hJ'
    rw [Finset.sum_singleton] at hexp
    have hu : IsUnit (evalE U.toUnifPre (τ 0) (𝟙 _) y J J') := by
      rw [hexp]
      exact (hg0 ▸ hx0 : IsUnit (sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J)).mul (Units.isUnit _)
    have hs : IsUnit (sval (τ 0) (𝟙 _) y J') := isUnit_of_mul_isUnit_right hu
    refine (isUnit_gs_iff_mem (𝟙 _) y _ hyW _).1 ?_
    have e := (gs_res (𝟙 _) y (hle 0 i i') hyW ((τ 0).f ![i' 0, i 0])).trans
      (sec_trans (τ 0) (𝟙 _) y (hle 0 i i' hyW) (Good.mem (L := U.LG.L) hJ' _ (𝟙 _)))
    exact e ▸ (Units.isUnit _).mul hs

end GlobalTheory.MumMult
end
end
