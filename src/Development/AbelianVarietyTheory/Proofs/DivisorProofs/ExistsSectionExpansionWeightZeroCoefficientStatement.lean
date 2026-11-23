module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemSpanCstOfCstMulEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppCompEqZeroOfGermDvd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam.CoordPow

theorem pow_law {X Q : Type} [AddCommGroup X] [CommGroup Q] (p : X → Q) (t : X → X → Q)
    (ht : ∀ a b, t a b = p (a + b) * (p a)⁻¹ * (p b)⁻¹) (hadd : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hev : ∀ χ, p (-χ) = p χ) (k : ℕ) (α μ : X) : p (α + k • μ) = p α * (p μ ^ k * t μ α) ^ k := by
  have hsym : ∀ a b, t a b = t b a := fun a b => by rw [ht, ht, add_comm, mul_right_comm]
  have h0 : ∀ b, t 0 b = 1 := fun b => by
    have := hadd 0 0 b
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp0 : p 0 = 1 := by
    have := ht 0 0
    rw [h0, add_zero, mul_inv_cancel, one_mul] at this
    exact inv_eq_one.1 this.symm
  have hneg : ∀ a b, t (-a) b = (t a b)⁻¹ := fun a b => by
    have := hadd a (-a) b
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hmm : t μ μ = p μ ^ 2 := by
    have e1 := hneg μ μ
    rw [hsym, ht, add_neg_cancel, hp0, hev, one_mul] at e1
    rw [← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]
  have hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n) := fun n => by
    induction n with
    | zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]
    | succ n ih =>
      have e := ht (α + n • μ) μ
      have e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n := by
        rw [hadd, hsym α μ, hn, hmm]
      have e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ := by
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul,
        show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]
      simp only [pow_add, pow_one]
      ac_rfl
  rw [key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJc : IntegralCharts D J)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, (val t (jK R ≫ q) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _
  have := hJc (q ≫ φ k) (hq k)
  simp only [Category.assoc]
  exact this

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem pull_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (h : (TK R).left ⟶ Y) (hh : h = jK R ≫ q) :
    ∃ u : Rˣ, (val (LB.pullGen D.P.L φ ε t h) (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  rw [val_pull hJ]
  have e : 𝟙 (TK R).left ≫ h = jK R ≫ q := by rw [hh]; exact Category.id_comp _
  rw [e]
  exact val_unit D ξ hJc t q hq

theorem rig_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) : ∃ u : Rˣ, (val D.rigK (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_
  · rw [Category.id_comp]
    unfold eSec
    exact Over.w _
  · rw [Over.toUnit_left, Category.comp_id]; rfl

omit [IsLocalRing R] in
theorem cub_hq (D : DegPre R) (a a' b : D.X) (I : thK) :
    ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ thφ D.P.A (x3 D.P.A) I) ≫ D.P.A.hom = 𝟙 _ := by
  show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _
  rw [← Over.comp_left, Over.w]; rfl

omit [IsLocalRing R] in
theorem degenerationTriplePoint_eq_lift (D : DegPre R) (a a' b : D.X) :
    D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
  simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]

omit [IsLocalRing R] in
open MonObj in
theorem sym_hq (D : DegPre R) (χ : D.X) (k : Fin 2) :
    ((D.c χ).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k) ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k
  · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _
    rw [← Over.comp_left, Over.w]; rfl
  · show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _
    rw [Category.comp_id, Over.w]; rfl

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (k : ℕ)
    (α mu : D.toPre.X) (r s : R), PsiCoord D.toPre α r → PsiCoord D.toPre (α + k • mu) (r * s) →
    ∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.toPre.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D.toPre J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s) := by
  intro R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc
  let H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    (Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range
  have mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H := fun ⟨u, hu⟩ =>
    ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩
  let π := QuotientGroup.mk' H
  have π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1 := fun h =>
    (QuotientGroup.eq_one_iff _).2 (mem h)
  let P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J
  let T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J
  let Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val D.toPre.rigK (𝟙 _) ξ J
  have hZ : π Z = 1 := π1 (rig_unit D.toPre ξ hJ hJc)
  have law := pow_law (fun χ => π (P χ)) (fun a b => π (T a b))
    (fun a b => by
      show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹
      rw [show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b,
        map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])
    (fun a a' b => by
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))
      have e' := congrArg π e
      rw [map_mul, map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm)
    (fun χ => by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))
      have e' := congrArg π e
      rw [map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm) k α mu
  set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J
  have hv : v = P mu ^ k * T mu α * Z ^ k :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl))
      (map_pow _ _ _))
  have hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]
    rw [law]
    exact mul_inv_eq_one.2 (mul_comm _ _)
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨u₁, h₁⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα
  obtain ⟨u₂, h₂⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk
  have e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹ := by
    rw [hw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1 := by
    rw [← map_mul, ← h₁]; exact Units.inv_mul _
  have hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨w * u₂ * u₁⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s *
    GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ *
    GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ)) * hA

end GlobalTheory.IntFam.CoordPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LeadZero

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.AdaptedSpan GlobalTheory.IntegralCombination GlobalTheory.PullbackValuation
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.UU GlobalTheory.IntFam GlobalTheory.IntFam.TermLift Formalism.L2.Pj

theorem intGen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsIntegrallyClosed R → ∀ (D : DegPre R) (k : ℕ), 1 ≤ k →
    ∀ (α mu : D.X) (s : R),
    (∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s)) →
    ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
      u₀.IsGen ∧ (∃ w : R, a ^ k = w * s) ∧ ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
  intro R _ _ _ hR D k hk α mu s hs
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (IntGen.basePts D (𝟙_ _) α mu) (IntGen.baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := IntGen.exists_genT D (𝟙_ _) (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := IntGen.multK_frac D k α mu v hv
  obtain ⟨a, ha, hak⟩ : ∃ a : R, r₁ = r₂ * a ∧ ∃ w : R, a ^ k = w * s := by
    have : IsProper D.P.A.hom := D.P.isAb.proper
    obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    obtain ⟨J, hJ, hJc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D.P.isLB D.P.A.hom
    obtain ⟨u, hu⟩ := hs ξ J hJ hJc
    have e := hr _ (𝟙 _) ξ J hJ
    have hσ : 𝟙 (TK R).left ≫ (toUnit (TK R)).left = jK R := by
      rw [Category.id_comp]; exact Over.w (toUnit (TK R))
    obtain ⟨w, hw⟩ : ∃ w : Rˣ, (val v (𝟙 _ ≫ (toUnit (TK R)).left) ξ J).val = GlobalTheory.PeriodBalance.cst ξ w := by
      rw [hσ]
      refine GlobalTheory.PeriodBalance.unit_gm ξ _ (Set.mem_iInter.2 fun i => ?_) _
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, IntGen.basePts D (𝟙_ _) α mu i = q.left := by
        fin_cases i <;> exact ⟨_, rfl⟩
      have := hJc (IntGen.basePts D (𝟙_ _) α mu i) (by rw [hq]; exact Over.w q)
      exact this
    have g : ∀ c : R, gs (𝟙 (TK R).left ≫ jK R) ξ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
        GlobalTheory.PeriodBalance.cst ξ c := fun c => by
      rw [Category.id_comp, gs_eq (jK R) ξ ⊤ trivial, GlobalTheory.PeriodBalance.cst_eq]; rfl
    rw [g, g, hw] at e
    have e2 : GlobalTheory.PeriodBalance.cst ξ (r₂ ^ k * ((u : R) * s)) = GlobalTheory.PeriodBalance.cst ξ ((r₁ * w) ^ k) := by
      rw [map_mul, map_pow, ← hu, ← mul_pow, e, map_pow, map_mul]
    have e3 := GlobalTheory.PeriodBalance.cst_injective ξ e2
    have e5 : r₁ ^ k = r₂ ^ k * ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      have hwk : ((w : R) * ((w⁻¹ : Rˣ) : R)) ^ k = 1 := by rw [Units.mul_inv, one_pow]
      linear_combination (-(((w⁻¹ : Rˣ) : R)) ^ k) * e3 - r₁ ^ k * hwk
    have := hR
    have inj := IsFractionRing.injective R (FractionRing R)
    have hr₂ : algebraMap R (FractionRing R) r₂ ≠ 0 := (map_ne_zero_iff _ inj).2 h₂
    have hr₂k : algebraMap R (FractionRing R) (r₂ ^ k) ≠ 0 := (map_ne_zero_iff _ inj).2 (pow_ne_zero _ h₂)
    have hx : (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) ^ k =
        algebraMap R (FractionRing R) ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      rw [div_pow, ← map_pow, ← map_pow, e5, map_mul, mul_div_cancel_left₀ _ hr₂k]
    have hint : IsIntegral R (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) :=
      IsIntegral.of_pow (by omega) (hx ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, inj ?_, (u : R) * ((w⁻¹ : Rˣ) : R) ^ k, inj ?_⟩
    · rw [map_mul, hy, mul_div_cancel₀ _ hr₂]
    · rw [map_pow, hy, hx, mul_right_comm]
  refine ⟨u₀, a, hu₀, hak, fun u hu hc Z r z J hJ => ?_⟩
  have key : gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₂) * (val u r z J).val =
      gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₁) *
        (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D (FractionRing R)).hom)
    let ρ : T' ⟶ DegPre.BF D (FractionRing R) := Over.homMk r rfl
    let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R))
      ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
    have e₁ := (gen_fe (D := D) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α).2 u hu hc T' ρ z J hJ
    have e₂ := vu₀ T' (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) z J hJ
    have e₃ : val (DegPre.famMult D (FractionRing R) k mu α) (ρ ≫ fst _ _).left z J =
        val (IntGen.multK D k mu α) κ.left z J :=
      val_pull hJ _ _ _
    have e₄ := hr _ κ.left z J hJ
    have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D (FractionRing R)).hom := Over.w κ
    have e₆ : κ.left ≫ (toUnit (TK R)).left =
        ((ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ toUnit _).left :=
      congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
    have e₇ : (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D (FractionRing R) := by
      rw [Category.assoc, whiskerRight_snd]
    have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom c) =
        gs (r ≫ (DegPre.BF D (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
      gs_pull r (DegPre.BF D (FractionRing R)).hom z ⊤ trivial _
    rw [e₅, e₆] at e₄
    rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
    rw [e₇] at e₂
    rw [g, g]
    exact IntGen.frac_mul e₁ e₂ e₄
  have sm : scal (DegPre.BF D (FractionRing R)).hom (r₂ * a) =
      scal (DegPre.BF D (FractionRing R)).hom r₂ * scal (DegPre.BF D (FractionRing R)).hom a := by
    simp only [Out.scal, map_mul]
  rw [ha, sm, gs_mul r z ⊤ trivial, _root_.mul_assoc] at key
  exact (GlobalTheory.FieldChange.isUnit_scal D h₂ r z).mul_left_cancel key

theorem termLift_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α mu : D.X)
    (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
    u₀.IsGen → (∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val) →
    ∀ (σ : SecAb D k α) (Φ : Fam D (FractionRing R) k), Φ.s α = pullAb D (FractionRing R) k α σ →
      ∃ f : SecAb D k (α + k • mu), pullAb D (FractionRing R) k (α + k • mu) (a • f) = Φ.s (α + k • mu) := by
  intro R _ _ D k α mu u₀ a hu₀ hrel σ Φ hΦ
  have hL := D.P.isLB
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨t, ht⟩ := exists_sec hL (formEq D k α mu)
    (pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _))
  refine ⟨(show SecAb D k (α + k • mu) from t), GlobalTheory.FieldBaseChange.sec_ext' hL fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG k mu α
  have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu α u hu hc) _ (𝟙 _) y J hJ
  have e₂ := hrel u hu hc _ (𝟙 _) y J hJ
  rw [e₁, e₂, hΦ, sval_pullAb _ _ _ _ hJ, sval_pullAb _ _ _ _ hJ, GlobalTheory.FieldBaseChange.sval_smul' hJ,
    ht _ _ y J hJ]
  erw [sval_pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _)
    (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) y hJ]
  rw [val_pull hJ, GlobalTheory.FieldBaseChange.gs_scal]
  have m₁ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (trB D mu).left =
      (𝟙 _ ≫ (DegPre.trF D (FractionRing R) mu).left) ≫ (DegPre.prB D (FractionRing R)).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left, trF_prB]
  have m₂ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (gB D).left =
      𝟙 _ ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, prB_gB]
  have m₃ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ D.P.A.hom = 𝟙 _ ≫ (DegPre.BF D (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [m₁, m₂, m₃]
  ring

theorem vanMod_smul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegPre R} {k : ℕ} {α : D.X}
    (c : R) (hc : c ∈ maximalIdeal R) (f : SecAb D k α) :
    VanMod (maximalIdeal R) (D := D) (k := k) (α := α) (c • f : SecAb D k α) 0 := fun j => by
  change ((fstG (maximalIdeal R) 0 D.P.A).left.app _).hom (Out.resTop _ (scal D.P.A.hom c) * f.f j) = 0
  rw [map_mul, GlobalTheory.ThickDiv.resTop_scal, GlobalTheory.ThickDiv.app_constFn_eq_zero _ 0 _ _ (by rwa [zero_add, pow_one]),
    zero_mul]



theorem exists_lead_members {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R)
    (D : DegData R (maximalIdeal R)) {k : ℕ} (hk : 1 ≤ k) (b : D.toPre.SecB k 0) :
    ∃ (Φ : Fam D.toPre (FractionRing R) k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom 1)) ∧
      f 0 = b ∧ ∀ α, α ≠ 0 → VanMod (maximalIdeal R) (f α) 0 := by
  classical
  have hR : IsIntegrallyClosed R := hB.1.2.2.1
  have hG := GlobalTheory.allSixLaws.1.globalFns
  have hcan : ∀ x y : D.toPre.X, k • x = k • y → x = y := fun x y h =>
    smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) (by simpa only [natCast_zsmul] using h)
  obtain ⟨Φ, hΦ, hΦ₀⟩ := UUA.exists_fam_rep (D := D.toPre) (F := FractionRing R) hG D.tau_bimult k 0
    (fun x y h => hcan x y (add_left_cancel h)) (pullAb D.toPre (FractionRing R) k 0 b)
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre 0).2 (GlobalTheory.PeriodFormCompare.psiIn_top D 0)
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.1
    (PsiCoordLocal.not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial
      (PsiCoordLocal.psiUnitOn_zero D.toPre D.tau_bimult) hr)
  have hf : ∀ α : D.toPre.X, ∃ f : SecAb D.toPre k α, pullAb D.toPre (FractionRing R) k α f = Φ.s α ∧
      (∀ h : α = 0, f = h ▸ b) ∧ (α ≠ 0 → VanMod (maximalIdeal R) (D := D.toPre) (k := k) (α := α) f 0) := fun α => by
    by_cases h0 : α = 0
    · subst h0
      exact ⟨b, hΦ.symm, fun _ => rfl, fun h => absurd rfl h⟩
    by_cases h1 : ∃ mu, 0 + k • mu = α
    · obtain ⟨mu, rfl⟩ := h1
      obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (0 + k • mu)).2
        (GlobalTheory.PeriodFormCompare.psiIn_top D _)
      have hm : r' ∈ maximalIdeal R := by
        obtain ⟨j, hj, h, e⟩ := hr'
        obtain ⟨s, hs, es⟩ := D.psi_pos _ h0 j ⊤ (isAffineOpen_top _) hj h
        obtain ⟨r'', hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ PsiCoordLocal.toOpen_top_bijective.2).1 hs
        have : r'' = r' := PsiCoordLocal.toOpen_top_bijective.1 (PsiCoordLocal.jK_app_inj ⊤ (es.trans e.symm))
        exact this ▸ hm
      have e : r' = r * ((hu.unit⁻¹ : Rˣ) * r') := by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
      rw [e] at hr'
      obtain ⟨u₀, c, hu₀, ⟨w, hw⟩, hrel⟩ := intGen_pow R hR D.toPre k hk 0 mu _
        (fun ξ J hJ hJc => GlobalTheory.IntFam.CoordPow.main R _ D k _ _ _ _ hr hr' ξ J hJ hJc)
      obtain ⟨f, hf⟩ := termLift_smul R D.toPre k 0 mu u₀ c hu₀ hrel b Φ hΦ
      have hc : c ∈ maximalIdeal R := Ideal.IsPrime.mem_of_pow_mem inferInstance k
        (hw ▸ Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hm))
      exact ⟨_, hf, fun h => absurd h h0, fun _ => vanMod_smul c hc f⟩
    · refine ⟨0, ?_, fun h => absurd h h0, fun _ j => map_zero _⟩
      rw [map_zero]
      exact SecOps.sec_ext fun j => (hΦ₀ α (fun mu h => h1 ⟨mu, h⟩) j).symm
  choose f hfK hf₁ hf₀ using hf
  refine ⟨Φ, f, fun α => ?_, hf₁ 0 rfl, hf₀⟩
  refine (secScal_iff_pullAb D.toPre _ (famAt D.toPre _ k α Φ) (f α) 1).2 ?_
  rw [map_one, one_smul]
  exact hfK α

end GlobalTheory.Mum.LeadZero

namespace GlobalTheory.Mum.LeadZero

theorem exists_expandsAt_lead_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  intro R _ _ _ hB D A G _ _ hG U k hk σ
  obtain ⟨Φ, f, hext, hf0, hvan⟩ := exists_lead_members hB D hk σ
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 Φ
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ hext α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨τ, hτ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ f h₁ hE
  refine ⟨τ, f, hf0, fun α hα j => (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt 0) _ _).2 (hvan α hα j), ?_⟩
  exact GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr τ σ₀ f f₀ hτ h₁ hE 0

end GlobalTheory.Mum.LeadZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_expansion_weightZero_coefficient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  first | exact @GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | exact GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | (intros; apply GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero <;> assumption)
end
end
