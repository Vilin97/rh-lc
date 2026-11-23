module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraitsStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTraitStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzeroStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOneStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamil

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_sec_exp_intFam_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  intro R _ _ _ hR D C F₁
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_map_thetaExpansion_all_traits R hR D C 0
  refine ⟨Φ F₁, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hΦ W T
  exact ⟨a, b, ha, hb, h F₁⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamilStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  first | exact @GlobalTheory.Mum.exists_sec_exp_intFam_one | exact GlobalTheory.Mum.exists_sec_exp_intFam_one | (intros; apply GlobalTheory.Mum.exists_sec_exp_intFam_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalarsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.coverTrait_expansion_scale_both_scalars : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  first | exact @GlobalTheory.Mum.Trait.exp_mul_left | exact GlobalTheory.Mum.Trait.exp_mul_left | (intros; apply GlobalTheory.Mum.Trait.exp_mul_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.ZeroFam

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval; exact (congrArg (gs r z _) (hs _)).trans (gs_zero' _ _ _)

theorem secB_zero_of_pullB {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x))
    (b' : D'.SecB k x) (hb : ∀ j, b.f j = 0) (h : PullB hD x b b') : ∀ q, b'.f q = 0 := by
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB
    ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ y))
  have e := h _ (𝟙 _) y p q (fun κ => hp κ) (fun κ => Set.mem_iInter.1 hy κ)
  rw [show b.f p = 0 from hb _] at e
  have e2 := e.symm.trans (gs_zero' _ _ _)
  exact ((Units.mul_right_eq_zero _).1 e2).trans (gs_zero' _ _ _).symm

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

open GlobalTheory.ExpInt

theorem section_eq_zero_of_expansion_zero_family {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ α j, (f α).f j = 0)
    (hE : ∀ e, U.ExpandsAt e k σ f) : ∀ j, σ.f j = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have ex : ∀ (φ' : Fin 1 → (pullback G.hom (jK W) ⟶ G.left))
      (_ : φ' = fun _ => pullback.fst G.hom (jK W) ≫ 𝟙 G.left),
      ∃ s' : LB.Sec (LB.LinComb U.LG.L φ' (fun _ => (k : ℤ))), ∀ z J, Good U.LG.L z J →
        sval s' (𝟙 _) z J = sval σ (pullback.fst G.hom (jK W)) z J := by
    rintro _ rfl
    exact ⟨pullSec _ _ _ σ _, fun z J hJ => (SectionScalarValuation.sval_pullSec _ _ σ _ (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩
  obtain ⟨s₀, hs₀⟩ := ex (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm)
  have h1 : scal (pullback.snd G.hom (jK W) ≫ jK W) (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have h1' : scal (DegPre.BF D.toPre (FractionRing W)).hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have hF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing W) α) (DegPre.famε k)
      ((0 : Fam D.toPre (FractionRing W) k).s α) (D.toPre.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D.toPre (FractionRing W)).left (scal (DegPre.BF D.toPre (FractionRing W)).hom 1) := fun α => by
    rw [h1']
    exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J _ =>
      (sval_eq_zero _ (hf α) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm
  have hE₀ : ∀ e, U.ExpandsAt e k (SecOps.secZero : H0 U.LG.L k) f := fun e => by
    refine ⟨∅, fun α _ j => by rw [show (f α).f j = 0 from hf α j, map_zero], fun p j₁ jf jt _ _ => ?_⟩
    simp only [Finset.attach_empty, Finset.sum_empty]
    erw [show (SecOps.secZero : H0 U.LG.L k).f j₁ = 0 from rfl, map_zero, map_zero, mul_zero]
  have hEs₀ : U.Expands k s₀ 0 := ⟨1, one_ne_zero, σ, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp]; exact (hs₀ y J hJ).symm, hF, hE⟩
  have hEz : U.Expands k SecOps.secZero 0 := ⟨1, one_ne_zero, SecOps.secZero, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm, hF, hE₀⟩
  have e₀ : s₀ = SecOps.secZero := ((U.expand k hk).2 0).unique hEs₀ hEz
  have hm := secIsMul_of_generic G U.LG.isLB k SecOps.secZero σ SecOps.secZero 1
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm)
    (by
      rw [h1]
      exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp, ← hs₀ y J hJ, e₀])
  intro j
  rw [hm j]
  exact mul_zero _

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

theorem exp_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  intro R _ _ _ _ D C W _ _ _ T k hk s F hF a b hExp b'
  obtain ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩ := hExp
  have hf' : ∀ x q, (f' x).f q = 0 := fun x => secB_zero_of_pullB T.hD x _ (f' x) (hF _) (hP x)
  have hσ' := section_eq_zero_of_expansion_zero_family T.U hk σ' f' hf' hE
  refine ⟨σ, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hP, hE⟩, hs⟩
  rw [hC Z r z J J' hJ hJ', sval_eq_zero _ hσ', mul_zero, mul_zero]

end GlobalTheory.Mum.ZeroFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  first | exact @GlobalTheory.Mum.ZeroFam.exp_of_members_zero | exact GlobalTheory.Mum.ZeroFam.exp_of_members_zero | (intros; apply GlobalTheory.Mum.ZeroFam.exp_of_members_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁ θ₀ hθ
  by_cases hz : ∀ α j, (F₁.f α).f j = 0
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => ?_⟩
    obtain ⟨a, b, ha, hb, h⟩ := hθ W T
    exact ⟨a, a, 1, ha, ha, GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero R hR D C W T 1 le_rfl θ₀ F₁ hz a b h a, by simp⟩
  push_neg at hz
  obtain ⟨G, S, hG, hS⟩ := GlobalTheory.T.exists_oddMultiplication_pullback_thetaFamily_degree_sq R hR D C m hm F₁ θ₀
  have hGz := hG hz
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  swap
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩
  obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
  obtain ⟨a₀, b₀, ha₀, hb₀, h₀⟩ := hθ W₀ T₀
  obtain ⟨v₀, hv₀⟩ := hS W₀ T₀ a₀ b₀ ha₀ h₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait R hR D C (m ^ 2) hk G S (Φ G) (fun W _ _ _ T => (hΦ W T).imp fun u hu => hu G)
    W₀ T₀ a₀ (b₀ * v₀) ha₀ (mul_ne_zero hb₀ v₀.ne_zero) hv₀
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hθ W T
  obtain ⟨v, hv⟩ := hS W T a b ha h
  obtain ⟨u, hu⟩ := hrt W T
  have htW : T.φ t ≠ 0 := fun h0 => ht (T.inj (h0.trans (map_zero _).symm))
  have h1 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G a (b * v) (T.φ t) hv
  have h2 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G (T.φ t) (T.φ r * u) a hu
  rw [mul_comm a (T.φ t)] at h2
  have he := GlobalTheory.T.expansion_secondScalar_determined_of_nonzero R hR D C W T (m ^ 2) hk S G hGz (T.φ t * a) _ _ (mul_ne_zero htW ha) h1 h2
  refine ⟨a, b, u * v⁻¹, ha, hb, h, ?_⟩
  have : b * T.φ t * v = a * T.φ r * u := by linear_combination he
  calc b * T.φ t = b * T.φ t * v * ↑v⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [this]; push_cast; ring

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  first | exact @GlobalTheory.Mum.ratio_odd_mul | exact GlobalTheory.Mum.ratio_odd_mul | (intros; apply GlobalTheory.Mum.ratio_odd_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraits

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, GlobalTheory.T.trait_expansionScalar_rescale_degreeOne R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_thetaSection_normalised_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  first | exact @GlobalTheory.Mum.exists_theta_unit_at_traits | exact GlobalTheory.Mum.exists_theta_unit_at_traits | (intros; apply GlobalTheory.Mum.exists_theta_unit_at_traits <;> assumption)
end
end
