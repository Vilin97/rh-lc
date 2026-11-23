module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClassStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegralStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.PartLe

theorem ubound {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab)
    (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {m : ℕ} (hm : S.N = m ^ 2) {a : S.Gam} {χ : u.D.toPre.X}
    (ha : l.yy a = QuotientAddGroup.mk χ) (hmin : ∀ v, l.q χ ≤ l.q (χ + m • v)) {T : AddSubgroup S.Gam}
    (hT : T = S.perp l.yy.ker) (w : T →+ ZMod S.N)
    (hw : ∀ t : T, w t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) (m • a)))
    {h : S.Gam} (hh : h ∈ l.yy.ker) (i : S.J) :
    ‖y₀ (∑ j, algebraMap o S.R (S.proj T w j i) * ⟨S.ev h j, S.ev_mem h j⟩)‖ ≤ S.delta y₀ * Real.exp (-l.q χ) := by
  subst hT
  have hsc : ∀ x, l.q (m • x) = (m : ℝ) ^ 2 * l.q x := fun x => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  have hm0 : (m : ℝ) ^ 2 ≠ 0 := by
    have := GlobalTheory.ZH.GlobalGen.N_pos S
    rw [hm] at this
    exact_mod_cast this.ne'
  have hlab : l.yy (m • a) = QuotientAddGroup.mk (m • χ) := by
    rw [map_nsmul, ha, QuotientAddGroup.mk_nsmul]
  have hwt : w = l.wt (m • χ) := AddMonoidHom.ext fun t => (hw t).trans (l.wt_eq _ _ hlab t).symm
  have key := GlobalTheory.ZH.WeightBound.main GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p
    y₀ u l hint (m • χ) (fun v => by
      have e : m • χ + S.N • v = m • (χ + m • v) := by rw [hm, smul_add, smul_smul, sq]
      rw [e, hsc, hsc]
      exact mul_le_mul_of_nonneg_left (hmin v) (sq_nonneg _)) h hh i
  have e : l.q (m • χ) / S.N = l.q χ := by
    rw [hsc, hm, Nat.cast_pow, mul_div_cancel_left₀ _ hm0]
  rw [e, ← hwt] at key

  simpa only [map_sum, map_mul] using key



theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ z₂ hz p _ c yy₁ _ y h hy yy hl _ a ν κ hν hmin
  subst hy
  obtain ⟨-, hHH⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X h1 h2 h3 h4 h5 h6 D.proj D.ε D.diag p _ (D.lift c y h) yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, hq, hyy, -⟩ := hl
  have hlift : ∀ (b : D.X.S.Gam) μ, yy b = QuotientAddGroup.mk μ → l.yy b = QuotientAddGroup.mk (j.symm μ) := by
    intro b μ hb
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    have e1 := hyy b χ hχ.symm
    rw [hb, QuotientAddGroup.eq] at e1
    obtain ⟨w, hw⟩ := e1
    rw [← hχ, eq_comm, QuotientAddGroup.eq]
    refine ⟨j.symm w, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hw ⊢
    rw [← map_nsmul, hw, map_add (f := _), map_neg, j.symm_apply_apply]
  have hker : yy.ker = l.yy.ker := by
    ext b
    simp only [AddMonoidHom.mem_ker]
    constructor
    · intro hb
      have := hlift b 0 hb
      rwa [map_zero] at this
    · intro hb
      have := hyy b 0 hb
      rwa [map_zero] at this
  have hint : ∀ a : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one rfl ((D.X.M.O _).algebraMap_mem a)
  have hδ0 := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ _ hb _ hz
  have hmem : GSum.lift D (y (cPt p)) (κ : X₁.S.Gam) ∈ l.yy.ker := by
    rw [← hker, hHH, GSum.lift]
    split_ifs with hex
    · exact hex.choose_spec.1
    · exact zero_mem _
  have key := ubound (S := D.X.S.rechart c₀ hc R' fg frac hth hev) u l hint (m := D.m) D.sq (hlift a ν hν) (fun v => by
      rw [hq, hq, map_add (f := _), map_nsmul, j.apply_symm_apply]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.2 (hmin _ ⟨j v, rfl⟩)) c.scale_pos.le)
    (T := D.X.S.TT D.X.M (y (cPt p))) (by rw [← hker, hHH]; rfl) (GSum.wtChar D _ a) (fun _ => rfl) hmem D.X.ρ.i₀
  rw [hq, j.apply_symm_apply, hy₀] at key
  unfold GSum.part
  generalize D.lab (GSum.base X₁ z₁) = x₀ at hx₀
  set Sg := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M (y (cPt p))) (GSum.wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (GSum.lift D (y (cPt p)) (κ : X₁.S.Gam)) j with hSg
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes rfl _
  have hle : (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ := by
    refine ciSup_le fun x => (congrArg norm (hy₀ _)).trans_le ?_
    show ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x)‖ ≤ _
    have e : c₀ * D.X.S.th x = D.X.S.th x / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
      have := hx₀.1
      field_simp
    rw [e, RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth _)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one rfl (hx₀.2 x))
  have hpos := hδ0.trans_le hle
  have hSR : c₀ * Sg ∈ R' := by
    rw [hSg, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    rw [mul_left_comm]
    exact mul_mem (R'.algebraMap_mem _) (hev _ _)
  have key' : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sg)‖ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ *
      Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le))
    congr 2
    rw [hSg, Finset.mul_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have hO : Sg / D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    obtain ⟨v, hv⟩ := ((RatModel.val_ne_zero_iff (RatModel.range_eq_singleton (gPt p ≫ y) _)
      ⟨c₀ * D.X.S.th x₀, hR' (hth x₀)⟩).1 (norm_pos_iff.1 hpos)).exists_right_inv
    have hv' : c₀ * D.X.S.th x₀ * (v : D.X.Ω₁) = 1 := congrArg Subtype.val hv
    have e : Sg / D.X.S.th x₀ = c₀ * Sg * v := by
      rw [div_eq_iff hx₀.1]
      linear_combination (-Sg) * hv'
    rw [e]
    exact mul_mem (hR' hSR) v.2
  have e : c₀ * Sg = Sg / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
    have := hx₀.1
    field_simp
  rw [e, RatModel.val_mul hsp hO (hR' (hth _)), norm_mul, mul_comm] at key'
  exact le_of_mul_le_mul_left key' hpos

end GlobalTheory.Poinc.PartLe
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExpStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weightPart_least_vector_norm_le_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.PartLe.main | exact GlobalTheory.Poinc.PartLe.main | (intros; apply GlobalTheory.Poinc.PartLe.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExpStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weightPart_unique_least_vector_attains_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.GSumEx.main | exact GlobalTheory.Poinc.GSumEx.main | (intros; apply GlobalTheory.Poinc.GSumEx.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperLevelValuesEqClassSumsPrescribedNorms

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GSumCls

theorem congMod_iff {X J : Type} [AddCommGroup X] (m : ℕ) (u v : J → X) :
    CongMod m u v ↔ ∀ i, CongMod m (u i) (v i) := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by rw [hw i]; rfl⟩

theorem norm_val_root_mul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hy : y (cPt p) = z) {u x : Ω} {k : ℕ} (hk : 0 < k)
    (hu : u ^ k = 1) (hx : x ∈ M.O z) : ‖M.val (gPt p ≫ y) (u * x)‖ = ‖M.val (gPt p ≫ y) x‖ := by
  haveI := RatModel.isIntegrallyClosed_O hM z
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : u ∈ M.O z := hv ▸ v.2
  have hs := RatModel.gPt_specializes hy
  have h1 : (⟨u, hmem⟩ : M.O z) ^ k = 1 := Subtype.ext hu
  have h2 : M.val (gPt p ≫ y) u ^ k = 1 := by
    have := congrArg (RatModel.valHomOf (gPt p ≫ y) z hs) h1
    rwa [map_pow, map_one] at this
  have h3 : ‖M.val (gPt p ≫ y) u‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 (by rw [← norm_pow, h2, norm_one])
  rw [RatModel.val_mul hs hmem hx, norm_mul, h3, one_mul]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem onto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) (ν : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk ν := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm ν))
  exact ⟨a, by simpa using hyy a _ ha⟩

theorem tendsto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) :
    Filter.Tendsto (fun ν : Fin 8 → c.T.D.toPre.X => c.sc * (qW W c.T.β ν : ℤ)) Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, hq, -⟩ := h
  refine (l.pos.comp j.symm.injective.tendsto_cofinite).congr fun ν => ?_
  rw [Function.comp_apply, hq, AddEquiv.apply_symm_apply]

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ z₂ hz
  obtain ⟨U, hU, hgeq⟩ := GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz
  refine ⟨U, hU, fun c yy₁ hlab => ?_⟩
  have hs : ∀ χ : Fin 8 → c.T.D.toPre.X, ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ (qW W c.T.β χ).toNat =
      Real.exp (-(c.sc * (qW W c.T.β χ : ℤ))) := fun χ => by
    have h0 := qW_nonneg_of_posW W X₁.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) χ
    rw [← c.exp_neg_sc_mul, ← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
  by_cases hex : ∃ y : Sp (OO p) ⟶ D.X.M.Z, y ≫ D.q = c.y ∧ y (cPt p) = z₂
  swap
  · refine ⟨fun μ _ => c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ^ (qW W c.T.β μ).toNat,
      fun μ _ => by rw [norm_pow, hs], fun μ => ⟨0, by rw [norm_pow, hs]⟩, fun y h hy => (hex ⟨y, h, hy⟩).elim⟩
  obtain ⟨y₀, h₀, hy₀⟩ := hex
  obtain ⟨yy₀, hlab₀, hcomp₀⟩ :=
    GLift.labels_lift g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c yy₁ hlab y₀ h₀
  choose a ha using onto_of_isLab hlab₀
  have hpart : ∀ b κ, GSum.part D z₁ z₂ b κ ∈ D.X.M.O z₂ := fun b κ => by
    rw [GSum.part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((D.X.M.O z₂).algebraMap_mem _)
      (GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ _ j z₂ hz)
  have hnorm : ∀ b κ, ‖D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ b κ)‖ =
      ‖D.X.M.val (gPt p ≫ y₀) (GSum.part D z₁ z₂ b κ)‖ := fun b κ => by
    obtain ⟨k, hk, hu⟩ := hU κ
    exact norm_val_root_mul (haveI := D.X.normal; GlobalTheory.IsNormalScheme.pred _) hy₀ hk hu (hpart b κ)
  have hsc := c.scale_pos
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms p (Fin 8 → c.T.D.toPre.X) (X₁.S.HH X₁.M z₁) D.m
    (fun ν => c.sc * (qW W c.T.β ν : ℤ)) _ _ (tendsto_of_isLab hlab) hs
    (fun ν κ => D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ (a ν) κ))
    (fun ν ν' κ h => hgeq p c yy₁ hlab y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ _ _ ν ν' κ (ha ν) (ha ν') h)
    (fun ν κ h => by
      rw [hnorm]
      refine GlobalTheory.T.weightPart_least_vector_norm_le_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν κ (ha ν) fun χ hχ => ?_
      exact_mod_cast le_of_mul_le_mul_left (h χ hχ) hsc)
    (fun ν h => by
      simp only [hnorm]
      refine GlobalTheory.T.weightPart_unique_least_vector_attains_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν (ha ν) fun χ hχ hne => ?_
      exact_mod_cast lt_of_mul_lt_mul_left (h χ hχ hne) hsc.le)
  refine ⟨t, ht1, ht2, fun y h hy yy hl hc b ν κ hb δ hδ => ?_⟩
  obtain ⟨S₀, hS₀⟩ := ht3 ν κ δ hδ
  refine ⟨S₀, fun S h1 h2 => ?_⟩
  rw [hgeq p c yy₁ hlab y h hy yy hl hc y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ b (a ν) ν ν κ hb (ha ν) ⟨0, by simp⟩]
  exact hS₀ S (fun χ hχ => (congMod_iff _ _ _).2 (h1 χ hχ)) fun χ hχ hcg => h2 χ hχ ((congMod_iff _ _ _).1 hcg)

end GlobalTheory.Poinc.GSumCls
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperLevelValuesEqClassSumsPrescribedNormsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deeperLevelValues_eq_classSums_prescribedNorms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  first | exact @GlobalTheory.Poinc.GSumCls.main | exact GlobalTheory.Poinc.GSumCls.main | (intros; apply GlobalTheory.Poinc.GSumCls.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnity

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.GSum.terms_and_sums : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ :=
  GlobalTheory.T.deeperLevelValues_eq_classSums_prescribedNorms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ) := by
  first | exact @GlobalTheory.Poinc.GSum.terms_and_sums | exact GlobalTheory.Poinc.GSum.terms_and_sums | (intros; apply GlobalTheory.Poinc.GSum.terms_and_sums <;> assumption)
end
end
