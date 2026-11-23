module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftTraces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftValuation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisation

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPull

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem trPt_aF (oa : D.toPre.OAct O) (a : O) (b b' : TF (R := V) F ⟶ D.toPre.P.A)
    (hb : b' = b ≫ oa.onB.act a) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trPt D.toPre F b' := by
  have := oa.onB.hom a
  have ap : aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
    simp [aF, DegPre.prB]
  have af : aF D F oa a ≫ fst (TF (R := V) F) D.toPre.P.A = fst _ _ := lift_fst _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, af, tr_fst, Category.assoc, tr_fst, af]
  · show (DegPre.trPt D.toPre F b ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      (aF D F oa a ≫ DegPre.trPt D.toPre F b') ≫ DegPre.prB D.toPre F
    rw [Category.assoc, ap, ← Category.assoc, tr_pr, MonObj.mul_comp, Category.assoc, ← hb,
      Category.assoc, tr_pr, MonObj.comp_mul, ap, ← Category.assoc, af]

theorem gen_eq_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hy : p₁.y = star a • p'.y) (hb : p'.g.b = p₁.g.b ≫ oa.onB.act a)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ + p'.y)) (pullε k N))) (huχz : uχz.IsGen)
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k))) (hΨ : Ψ.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p₁.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val Ψ (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, trPt_aF oa a p₁.g.b p'.g.b hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ + p'.y))
      (fun i => (aF D F oa a).left ≫ DegPre.phiφ D.toPre F p'.y χ p'.g.b i)) (Sum.elim (pullε k N) (DegPre.deltaε k))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p₁.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b)) (Sum.elim (pullε k N) (DegPre.deltaε (k * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hΨ _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key

theorem exists_normalisation (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (b b' : TF (R := V) F ⟶ D.toPre.P.A) (hb : b' = b ≫ oa.onB.act a)
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b') (DegPre.lineε k))) (hw' : w'.IsGen)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (k * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b :=
    CanonicalLiftTraces.zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = b' := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have hN' : ((k * (N - 1) : ℕ) : ℤ) = ((k * N : ℕ) : ℤ) - k := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]; push_cast; ring
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (k * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1]
      simp only [CanonicalLiftTraces.comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val,
        DegPre.famε, smul_zero, c0, _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) w')
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _) hw')
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]

theorem gen_eq_at_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hgt : GtAct oa a p₁.g p'.g)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))))
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p₁.g.b).left y J)⁻¹)
    (χ ξ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a ξ) (pullε k N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k)))
    (hcΨ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Ψ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p'.g.s χ) w'))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p₁.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hros := oa.onB.rosati (star a)
  rw [star_star] at hros
  obtain ⟨r, hr, hr0⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hros
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p₁.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p₁.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcΨ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e2
  have e3 := val_corr hJ hcΦ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e3
  have e5 := hwv y J hJ
  rw [Over.comp_left] at e5
  have e6 := val_corr hJ (hgt.2 r hr hr0 χ) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at e6
  have e7 : val Ψ ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val Ψ (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ, e3,
    CanonicalLiftValuation.pull_val_chi hG oa a k N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl,
    e5, e7, e1, e2, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiRel_pullAl : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (p' : QkPt D.toPre F k) (p₁ : QkPt D.toPre F (k * N)), GtAct oa a p₁.g p'.g → p₁.y = star a • p'.y → ∀ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen → ∃ w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))), w₁.IsGen ∧ ∀ (s t : Fam D.toPre F k) (s' t' : Fam D.toPre F (k * N)), PhiRel D.toPre F k p' w' s t → PullAl D F oa a k N s s' → PullAl D F oa a k N t t' → PhiRel D.toPre F (k * N) p₁ w₁ s' t' := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw0 a N k hN _ haa p' p₁ hgt hy w' hw'
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := hw0
  obtain ⟨u0, hu0, hc0⟩ := exists_pullGen D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k 0
  obtain ⟨w, hw, hwv⟩ := exists_normalisation oa a k N hN p₁.g.b p'.g.b hgt.1 w' hw' u0 hu0
  refine ⟨w, hw, fun s t s' t' hst hs' ht' => ?_⟩
  rw [phiRel_iff hG p₁ w hw s' t']
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := ht'.1 (χ + p'.y)
    obtain ⟨uχ, huχ, hc, hs⟩ := hs'.1 χ
    obtain ⟨⟨Ψ, hΨ, hcΨ⟩, -⟩ := gen_phi hG p' w' hw' χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p₁ w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ Ψ).1 (hst χ Ψ hΨ hcΨ) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trPt D.toPre F p'.g.b).left := by
      rw [← Over.comp_left, Category.assoc, trPt_aF oa a p₁.g.b p'.g.b hgt.1, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := gen_eq_of_origin hG oa a k N p' p₁ hy hgt.1 χ uχ huχ uχz huχz Ψ hΨ Φ hΦ
      (fun y J hJ => gen_eq_at_origin hG oa a k N p' p₁ hgt u0 hu0 hc0 w' w hwv χ _ uχ huχ hc uχz hcz Ψ hcΨ
        Φ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val Ψ (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ - p'.y, ?_⟩
      rw [smul_sub, ← h, ← hβ, hy]
      abel
    rw [CanonicalLiftFrobenius.sval_zero _ (ht'.2 β hβn), CanonicalLiftFrobenius.sval_zero _ (hs'.2 a' (fun χ h => ha ⟨χ, h⟩)),
      MulZeroClass.zero_mul]

end GlobalTheory.ThetaPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorOnPullbackEqSum

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGenerators

open TorusExt

attribute [local instance] gtGroup

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem exists_lift (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (a : O) (N k : ℕ)
    (haa : a * star a = (N : O)) (u v : O) (huv : u * N + v * k = 1) (p : QkPt D F k) :
    ∃ (p' : QkPt D F k) (p₁ : QkPt D F (k * N)), QkPt.Equiv D F p p' ∧ GtAct oa a p₁.g p'.g ∧
      p₁.y = star a • p'.y ∧ ∀ b : O, QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) →
        QkPt.Equiv D F (qkZero hB F (k * N)) (qkSmul hB hG oa b p₁) := by
  letI := gtModule hG oa F
  have hs : ∀ (c : O) (g : GtPtF D F), gtSmul hG oa c g = c • g := fun _ _ => rfl
  have hι : ∀ (c : O) (y : D.X), iota hB F (c • y) = c • iota hB F y := iota_smul hG oa hB
  have hp : (k : O) • p.g = iota hB F p.y := by rw [Nat.cast_smul_eq_nsmul]; exact qk_nsmul hB p
  have e : u * N = 1 + k * -v := by linear_combination huv
  refine ⟨qkSmul hB hG oa (u * N) p, qkMk hB (star a • (u * N) • p.y) ((u * star a) • p.g) ?_, ?_, ?_, rfl, ?_⟩
  · rw [hι, hι, ← hp, ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · refine (equiv_iff hB _ _).2 ⟨(-v) • p.y, ?_, ?_⟩
    · show (u * N) • p.y = p.y + k • (-v) • p.y
      rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    · show (u * N) • p.g = p.g + iota hB F ((-v) • p.y)
      rw [hι, ← hp, e, add_smul, one_smul, mul_comm, mul_smul]
  · refine (gtAct_iff_eq_gtSmul hG oa _ _ _).2 ?_
    show (u * N) • p.g = a • (u * star a) • p.g
    rw [smul_smul, ← haa]
    congr 1
    ring
  · intro b hb
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 hb
    have hy' : b • p.y = (k : O) • z := by
      rw [Nat.cast_smul_eq_nsmul]; exact hy.trans (zero_add _)
    have hg' : b • p.g = iota hB F z := hg.trans (zero_add _)
    refine (equiv_iff hB _ _).2 ⟨(u * star a) • z, ?_, ?_⟩
    · show b • star a • (u * N) • p.y = 0 + (k * N) • (u * star a) • z
      rw [zero_add, smul_comm b, smul_comm b, hy', ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · show b • (u * star a) • p.g = 0 + iota hB F ((u * star a) • z)
      rw [zero_add, smul_comm b, hg', hι]

theorem killed_iff (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} {G : Type} [Group G]
    (f : QkPt D F k → G) (act : O → G → G) (h₁ : ∀ p p', f p = f p' ↔ QkPt.Equiv D F p p')
    (h₂ : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p')
    (h₃ : ∀ a p p', QkAct oa a p p' → f p' = act a (f p)) (b : O) (p : QkPt D F k) :
    act b (f p) = 1 ↔ QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) := by
  have z : f (qkZero hB F k) = 1 := by
    have e : qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k := qk_ext (add_zero _) (add_zero _)
    have := h₂ _ _ _ (qkAdd_qkAdd hB (qkZero hB F k) (qkZero hB F k))
    rw [e] at this
    exact left_eq_mul.1 this
  rw [← h₁, z, h₃ b p _ (qkAct_qkSmul hB hG oa b p), eq_comm]

end Points

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem exists_operator (hL : Laws) (oa : D.toPre.OAct O) (w0 : O) (hw0 : TraceFormTwistIso D.toPre oa w0) (a : O) (N k : ℕ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (haa : a * star a = (N : O))
    (π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N)) (hπ : Function.Injective π)
    (hπ' : ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s) (θ : Fam D.toPre F k) (hθ : θ ≠ 0)
    (p p' : QkPt D.toPre F k) (p₀ p₁ p₂ : QkPt D.toPre F (k * N)) (he : QkPt.Equiv D.toPre F p p')
    (hg : GtAct oa a p₁.g p'.g) (hy : p₁.y = star a • p'.y) (hy₂ : p₂.y = p₀.y + p₁.y) (hg₂ : p₀.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (w₀ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε (k * N)))) (hw₀ : w₀.IsGen)
    (ζ ζ₀ : F) (hζ : FinOrd D F k p w ζ) (hζ₀ : FinOrd D F (k * N) p₀ w₀ ζ₀) :
    ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε (k * N))), w₂.IsGen ∧
      FinOrd D F (k * N) p₂ w₂ (ζ₀ * ζ) ∧ ∀ s t t', PhiRel D.toPre F k p w s t →
        PhiRel D.toPre F (k * N) p₀ w₀ (π t) t' → PhiRel D.toPre F (k * N) p₂ w₂ (π s) t' := by
  have hkN : 1 ≤ k * N := Nat.mul_pos hk hN
  obtain ⟨w', hw', h'⟩ := phiRel_of_qkEquiv hL V D F k hk p p' he w hw
  obtain ⟨w₁, hw₁, h₁⟩ := ThetaPull.phiRel_pullAl hL V D F O oa w0 hw0 a N k hN hk haa p' p₁ hg hy w' hw'
  obtain ⟨w₂, hw₂, h₂⟩ := phi_mul hL V D F (k * N) hkN p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ hw₀ hw₁
  have hc : ∀ s t, PhiRel D.toPre F k p w s t → PhiRel D.toPre F (k * N) p₁ w₁ (π s) (π t) := fun s t h =>
    h₁ s t _ _ ((h' s t).1 h) ((hπ' _ _).2 rfl) ((hπ' _ _).2 rfl)
  refine ⟨w₂, hw₂, ?_, fun s t t' h h₀ => h₂ _ _ _ (hc s t h) h₀⟩
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V _ D F k hk p w hw
  obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of hL V _ D F (k * N) hkN p₁ w₁ hw₁
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 hζ
  have hn : ∀ (n : ℕ) (s : Fam D.toPre F k), ((ζ • Φ₁ : Module.End F (Fam D.toPre F (k * N))) ^ n) (π s) =
      π (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ n) s) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul π, (hΦ₁ _ _).1 (hc s _ ((hΦ _ _).2 rfl))]
  obtain ⟨c₁, c₂⟩ := finOrd_criteria hL V D F (k * N) hkN
  refine c₂ p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ w₂ hw₀ hw₁ hw₂ h₂ ζ₀ ζ hζ₀
    (c₁ p₁ w₁ hw₁ ζ Φ₁ hΦ₁ (π θ) M (fun h => hθ (hπ (h.trans (map_zero π).symm))) hM ?_)
  exact (hn M θ).trans (by rw [hU]; rfl)

end GlobalTheory.ThetaGenerators

namespace GlobalTheory


open ThetaGenerators TorusExt in
theorem operator_on_pullback_eq_sum : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (θ' s : Fam P.D.toPre F (1 * N')) (θ₂ s₂ t₀ h : Fam P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl P.D F P.oD a (1 * N') N θ' θ₂ → PullAl P.D F P.oD a (1 * N') N s s₂ → ∀ (m : ℕ) (c : Fin m → F) (p : Fin m → QkPt P.D.toPre F (1 * N')) (x : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b) (DegPre.lineε (1 * N')))) (ζ : Fin m → F) (tt : Fin m → Fam P.D.toPre F (1 * N')), ((∀ i, P.ToA F (1 * N') (p i) (x i)) ∧ (∀ i, x i ≫ P.oA.act (star (a')) = 1) ∧ (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N') (p i) (w i) (ζ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N'), PhiRel P.D.toPre F (1 * N') (p i) (w i) θ' t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (tt i)) ∧ s = ∑ i, c i • tt i) → ∀ (p₀ : QkPt P.D.toPre F (1 * N' * N)) (x₀ : TFK (R := V) F ⟶ P.A.A) (w₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₀.g.b) (DegPre.lineε (1 * N' * N)))) (ζ₀ : F), P.ToA F (1 * N' * N) p₀ x₀ → x₀ ≫ P.oA.act (star a) = 1 → w₀.IsGen → ζ₀ ≠ 0 → FinOrd P.D F (1 * N' * N) p₀ w₀ ζ₀ → PhiRel P.D.toPre F (1 * N' * N) p₀ w₀ s₂ t₀ → Fam.IsSmul P.D.toPre F ζ₀ t₀ h → ∃ (p₂ : Fin m → QkPt P.D.toPre F (1 * N' * N)) (x₂ : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w₂ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₂ i).g.b) (DegPre.lineε (1 * N' * N)))) (ζ₂ : Fin m → F) (t₂ : Fin m → Fam P.D.toPre F (1 * N' * N)), (∀ i, P.ToA F (1 * N' * N) (p₂ i) (x₂ i)) ∧ (∀ i, x₂ i ≫ P.oA.act (star (a' * a)) = 1) ∧ (∀ i, (w₂ i).IsGen ∧ ζ₂ i ≠ 0 ∧ FinOrd P.D F (1 * N' * N) (p₂ i) (w₂ i) (ζ₂ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N' * N), PhiRel P.D.toPre F (1 * N' * N) (p₂ i) (w₂ i) θ₂ t' ∧ Fam.IsSmul P.D.toPre F (ζ₂ i) t' (t₂ i)) ∧ h = ∑ i, c i • t₂ i := by
  intro hL E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro a a' N N' hN hN' hco haa _ F _ _ _ θ' s θ₂ s₂ t₀ h hθ hθ₂ hs₂ m c p x w ζ tt ⟨hx, hxa, hw, htt, hs⟩
    p₀ x₀ w₀ ζ₀ hx₀ hxa₀ hw₀ hζ₀ hf₀ ht₀ hh
  have hG := hL.globalFns
  have hB := P.D.tau_bimult
  have hk : 1 ≤ 1 * N' := by omega
  have hkN : 1 ≤ 1 * N' * N := Nat.mul_pos hk hN
  obtain ⟨u, v, huv⟩ : IsCoprime (N : 𝓞 E) ((1 * N' : ℕ) : 𝓞 E) := by
    rw [_root_.one_mul]; exact hco.cast
  obtain ⟨π, hπ, hπ'⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a N (1 * N') hN hk haa
  obtain rfl := (hπ' _ _).1 hθ₂
  obtain rfl := (hπ' _ _).1 hs₂
  obtain ⟨f, f₀, -, f₁, f₂, f₃, -⟩ := hT F (1 * N') hk
  obtain ⟨g, g₀, -, g₁, g₂, g₃, -⟩ := hT F (1 * N' * N) hkN
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of hL V _ P.D F (1 * N' * N) hkN p₀ w₀ hw₀
  choose p' p₁ he hg hy hb using fun i => exists_lift hG hB P.oD a N (1 * N') haa u v huv (p i)
  choose w₂ hw₂ hf₂ hΦ₂ using fun i => exists_operator hL P.oD H.w0 P.w0 a N (1 * N') hN hk haa π hπ hπ' θ' hθ
    (p i) (p' i) p₀ (p₁ i) (qkAdd hB p₀ (p₁ i)) (he i) (hg i) (hy i) rfl ((isAdd_iff_eq _ _ _).2 rfl)
    (w i) (hw i).1 w₀ hw₀ (ζ i) ζ₀ (hw i).2.2 hf₀
  choose t' ht' htt' using htt
  refine ⟨fun i => qkAdd hB p₀ (p₁ i), fun i => g (qkAdd hB p₀ (p₁ i)), w₂, fun i => ζ₀ * ζ i,
    fun i => (ζ₀ * ζ i) • Φ₀ (π (t' i)), fun i => (g₀ _ _).2 rfl, fun i => ?_,
    fun i => ⟨hw₂ i, mul_ne_zero hζ₀ (hw i).2.1, hf₂ i⟩,
    fun i => ⟨_, hΦ₂ i _ _ _ (ht' i) ((hΦ₀ _ _).2 rfl), (DVR.isSmul_iff _ _ _).2 rfl⟩, ?_⟩
  · have k₁ : g (p₁ i) ≫ P.oA.act (star a') = 1 :=
      (killed_iff hG hB P.oD g (fun b y => y ≫ P.oA.act b) g₁ g₂ g₃ (star a') (p₁ i)).2 (hb i _
        ((killed_iff hG hB P.oD f (fun b y => y ≫ P.oA.act b) f₁ f₂ f₃ (star a') (p i)).1
          ((f₀ _ _).1 (hx i) ▸ hxa i)))
    have := P.oA.hom (star (a' * a))
    have := P.oA.hom (star a')
    have := P.oA.hom (star a)
    have e₀ : x₀ ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa₀, MonObj.one_comp]
    have e₁ : g (p₁ i) ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul, P.oA.map_mul, ← Category.assoc, k₁, MonObj.one_comp]
    show g (qkAdd hB p₀ (p₁ i)) ≫ P.oA.act (star (a' * a)) = 1
    rw [g₂ _ _ _ (qkAdd_qkAdd hB p₀ (p₁ i)), ← (g₀ _ _).1 hx₀, MonObj.mul_comp, e₀, e₁, _root_.mul_one]

  · rw [(DVR.isSmul_iff _ _ _).1 hh, (hΦ₀ _ _).1 ht₀, hs, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(DVR.isSmul_iff _ _ _).1 (htt' i), map_smul, map_smul, map_smul, map_smul, smul_comm, smul_smul ζ₀]

end GlobalTheory
end
end
end
