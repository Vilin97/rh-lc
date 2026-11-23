module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsRatioOnComponentOfBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
public import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBoundStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmul

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Filter
open scoped ENNReal NNReal

namespace GlobalTheory.GrowthMul

theorem limsup_le_iSup_classes {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ≥0∞) :
    limsup f atTop ≤ ⨆ j : Fin a, limsup (fun k => f (a * k + j)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
  have h1 : ∀ j : Fin a, ∀ᶠ k in atTop, f (a * k + j) < x := fun j =>
    eventually_lt_of_limsup_lt ((le_iSup (fun j : Fin a => limsup (fun k => f (a * k + j)) atTop) j).trans_lt hx)
  choose K hK using fun j => eventually_atTop.1 (h1 j)
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨a * Finset.univ.sup K, fun τ hτ => ?_⟩)
  have hm : τ % a < a := Nat.mod_lt _ (by omega)
  have hq : Finset.univ.sup K ≤ τ / a := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hτ)
  have := hK ⟨τ % a, hm⟩ (τ / a) ((Finset.le_sup (Finset.mem_univ _)).trans hq)
  rw [Nat.div_add_mod] at this
  exact this.le

theorem term_mul_eq (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) {k : ℕ} (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      (a : ℝ≥0∞) ^ D * ((D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / ((a * k : ℕ) : ℝ≥0∞) ^ D) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  rw [Nat.cast_mul, mul_pow, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ha0 hat, mul_comm]

theorem growth_mul_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) :
    growth D (fun k => r (a * k)) ≤ (a : ℝ≥0∞) ^ D * growth D r := by
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  set g : ℕ → ℝ≥0∞ := fun τ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D
  have h1 : growth D (fun k => r (a * k)) = limsup (fun k => (a : ℝ≥0∞) ^ D * g (a * k)) atTop :=
    limsup_congr ((eventually_ge_atTop 1).mono fun k hk => term_mul_eq D ha r hk)
  rw [h1, ENNReal.limsup_const_mul_of_ne_top hat, growth]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have ht : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  exact (limsup_comp g (fun k => a * k) atTop).le.trans (limsup_le_limsup_of_le ht)

theorem limsup_class_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) (j c : ℕ)
    (h : ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    limsup (fun k => (D.factorial : ℝ≥0∞) * (r (a * k + j) : ℝ≥0∞) / ((a * k + j : ℕ) : ℝ≥0∞) ^ D) atTop ≤
      ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hit : ((a : ℝ≥0∞) ^ D)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
  refine (limsup_le_limsup ((eventually_ge_atTop 1).mono fun k hk => ?_)).trans
    ((ENNReal.limsup_const_mul_of_ne_top hit).le.trans (by gcongr; exact GlobalTheory.GrowthShift.growth_shift_le D c _))
  show _ ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D)
  have hk0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hkt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have e : ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D) =
      (D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / ((a : ℝ≥0∞) ^ D * (k : ℝ≥0∞) ^ D) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
    ring
  rw [e]
  refine ENNReal.div_le_div (by gcongr; exact h k) ?_
  rw [← mul_pow]
  gcongr
  exact_mod_cast Nat.le_add_right _ _

theorem growth_mul_eq_of_classes (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞)
    (h : ∀ j, j < a → ∃ c, ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    growth D (fun k => r (a * k)) = (a : ℝ≥0∞) ^ D * growth D r := by
  refine le_antisymm (growth_mul_le D ha r) ?_
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have h1 : growth D r ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
    refine (limsup_le_iSup_classes ha _).trans (iSup_le fun j => ?_)
    obtain ⟨c, hc⟩ := h j j.2
    exact limsup_class_le D ha r j c hc
  calc (a : ℝ≥0∞) ^ D * growth D r ≤ (a : ℝ≥0∞) ^ D * (((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = growth D (fun k => r (a * k)) := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem pow_mul_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ τ : ℕ} {g f : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hf : f ∈ cuspOn U Z (τ • G)) (n : ℕ) :
    g ^ n * f ∈ cuspOn U Z ((τ + n * τ₀) • G) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have e : (τ + (n + 1) * τ₀) • G = (τ + n * τ₀) • G + τ₀ • G := by rw [← add_nsmul]; ring_nf
    rw [e, pow_succ, mul_right_comm]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (GlobalTheory.DegTop.even_nsmul hG _) (GlobalTheory.DegTop.even_nsmul hG _) ih hg.1

set_option synthInstance.maxHeartbeats 100000 in
theorem rank_le_of_ne_zero {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ : ℕ} {g : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hg0 : g ≠ 0) (τ n : ℕ) :
    Module.rank c.F (cuspOn U Z (τ • G)) ≤ Module.rank c.F (cuspOn U Z ((τ + n * τ₀) • G)) := by
  have hv : genVal Z g ≠ 0 := fun h0 => hg0 (GlobalTheory.DegTop.eq_zero_of_genVal hg h0)
  let m := (genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (g ^ n)
  have hpow : genVal Z (g ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hv
  have hinj : Function.Injective (m ∘ₗ (cuspOn U Z (τ • G)).subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [injective_iff_map_eq_zero]
    intro f hf
    have hzero : genVal Z (g ^ n * f) = 0 := hf
    rw [map_mul] at hzero
    exact Subtype.ext (GlobalTheory.DegTop.eq_zero_of_genVal f.2
      ((mul_eq_zero.1 hzero).resolve_left hpow))
  have hrank : Module.rank c.F ((cuspOn U Z (τ • G)).map m) =
      Module.rank c.F (cuspOn U Z (τ • G)) := by
    rw [← rank_range_of_injective _ hinj, LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrank]
  refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, pow_mul_mem_cuspOn hG hg hf n, rfl⟩

theorem classes_bound (Z : Comp Xo c) {G : WTZ E} (hG : Even G.2) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ∃ c' : ℕ, ∀ k, Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k + j) • G))) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * (k + c')) • G))) := by
  by_cases hex : ∃ q : ℕ, ∃ g ∈ cuspOn U Z ((a * q + j) • G), g ≠ 0
  · obtain ⟨q, g, hg, hg0⟩ := hex
    refine ⟨j + (a - 1) * q, fun k => ?_⟩
    have e : a * (k + (j + (a - 1) * q)) = (a * k + j) + (a - 1) * (a * q + j) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    exact OrderHomClass.mono Cardinal.toENat (rank_le_of_ne_zero hG hg hg0 _ _)
  · push_neg at hex
    refine ⟨0, fun k => ?_⟩
    have h0 : cuspOn U Z ((a * k + j) • G) = ⊥ := (Submodule.eq_bot_iff _).2 (hex k)
    rw [h0, rank_bot, map_zero]
    exact zero_le

end GlobalTheory.GrowthMul

theorem GlobalTheory.GrowthMul.growthOn_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U _ Z G hG a ha
  rw [growthOn, growthOn]
  convert GlobalTheory.GrowthMul.growth_mul_eq_of_classes (dimFlag Dw) ha (fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))))
    (fun j _ => GlobalTheory.GrowthMul.classes_bound (U := U) Z hG ha j) using 4 with τ
  rw [smul_smul, mul_comm]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmulStatement

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.cuspFormGrowthOnComponent_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  first | exact @GlobalTheory.GrowthMul.growthOn_nsmul | exact GlobalTheory.GrowthMul.growthOn_nsmul | (intros; apply GlobalTheory.GrowthMul.growthOn_nsmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentFunctionFieldFg

section

@[expose] public section

set_option autoImplicit false

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem om_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG := by
  intro E _ _ _ H Dw l Xo c r U _ Z
  exact fnFG_of Xo c (kapFG_pf Xo c) Z

end GlobalTheory.DegVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentFunctionFieldFgStatement

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.flagSpaceComponent_functionField_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG := by
  first | exact @GlobalTheory.DegVal.om_fg | exact GlobalTheory.DegVal.om_fg | (intros; apply GlobalTheory.DegVal.om_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthLeImageDegreeLowerWeight

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem growthOn_le_compDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro E _ _ _ H Dw l Xo c r U hU Z G G' hG hG' hfin hB hM
    rcases eq_or_ne (growthOn U Z G') 0 with h0 | h0
    · rw [h0]; exact bot_le
    obtain ⟨a, θ, ha, hθ, hmul⟩ := hM
    letI : FiniteDimensional c.F (cuspOn U Z G) :=
      GlobalTheory.DegTop.finiteDimensional_of_growthOn (U := U) (Z := Z) hG hfin
    have hR := GlobalTheory.T.cuspFormsRatioOnComponent_of_birational E H Dw l Xo c r U Z G hB
    have hFG := GlobalTheory.T.flagSpaceComponent_functionField_fg E H Dw l Xo c r U hU Z
    set ev := genPoint Z (cuspOn U Z G) with hev
    let S : ℕ → Submodule c.F (Om Z) := fun k =>
      if k = 0 then ⊥ else (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k))
    have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.1 c.F _ _ ev (dimFlag Dw) a ha S (by
      intro k t ht
      by_cases hk : k = 0
      · simp only [S, hk, if_true, Submodule.mem_bot] at ht
        subst ht
        refine ⟨?_, ⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩⟩
        rw [IsIntDeg, map_zero, mul_zero]
        exact isIntegral_zero
      · simp only [S, hk, if_false] at ht
        obtain ⟨f, hf, rfl⟩ := ht
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
        obtain ⟨hc, hv⟩ := hmul k hk1 f hf
        exact ⟨GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound c.F _ _ ev inferInstance inferInstance hFG _ _ hv, hR _ _ hc⟩)
    have hθk : ∀ k : ℕ, genVal Z (θ ^ k) ≠ 0 := fun k => by rw [map_pow]; exact pow_ne_zero _ hθ
    have h2 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) ≤
        growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (S k))) :=
      GlobalTheory.DegTop.growth_mono _ fun k hk => by
        have hk0 : k ≠ 0 := by omega
        show _ ≤ Cardinal.toENat (Module.rank c.F (S k))
        have hS : S k = (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k)) := if_neg hk0
        rw [hS, GlobalTheory.DegTop.rank_map_mul (U := U) (G := (a * k) • G') (hθk k)]
    have hmulG : ∀ G₀ : WTZ E, growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G₀)))) =
        growthOn U Z (a • G₀) := fun G₀ => by
      rw [growthOn]
      congr 1
      funext k
      rw [mul_nsmul]
    have h3 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) =
        (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' := by
      rw [hmulG, GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G' hG' a ha]
    have h4 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≤ (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
      rw [← GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G hG a ha, ← hmulG]
      exact GlobalTheory.DegTop.growth_mono _ fun k hk => GlobalTheory.DegTop.hilb_le hG (Nat.mul_pos ha hk)
    have haD0 : (a : ℝ≥0∞) ^ dimFlag Dw ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
    have haDT : (a : ℝ≥0∞) ^ dimFlag Dw ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
    have hlow : (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' ≤ growth (dimFlag Dw) (fun k => hilb ev (a * k)) :=
      h3 ▸ h2.trans h1
    have hne0 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ 0 :=
      ne_bot_of_le_ne_bot (mul_ne_zero haD0 h0) hlow
    have hneT : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top haDT hfin) h4
    obtain ⟨δ, hδ⟩ := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.1 c.F _ _ ev (dimFlag Dw) a ha hne0 hneT
    rw [GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ ev (dimFlag Dw) a ha δ hδ] at hlow
    rw [compDeg, ← hev, hδ.imageDeg_eq]
    first | exact (ENNReal.mul_le_mul_iff_right haD0 haDT).1 hlow | exact (ENNReal.mul_le_mul_iff_left haD0 haDT).1 hlow

end GlobalTheory.DegVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthLeImageDegreeLowerWeightStatement

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.cuspFormGrowth_le_imageDegree_lowerWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  first | exact @GlobalTheory.DegVal.growthOn_le_compDeg | exact GlobalTheory.DegVal.growthOn_le_compDeg | (intros; apply GlobalTheory.DegVal.growthOn_le_compDeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem GlobalTheory.DegVal.compDeg_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → Proport U → EqVolume U → ∀ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) → (∀ τ, StrictAnti (uPrime Dw u τ)) → (∀ Z, BirOn U Z (wtOf Dw u 0)) → (∀ Z, ValMult U Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0)) → ∀ Z Z' : Comp Xo c, delPrime U Z' u ≤ compDeg U Z (wtOf Dw u 0) ∧ (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ delPrime U Z' u / (1 - rhoB Dw u) := by
  intro E _ _ _ H Dw l Xo c r U hU hP hV u hu hu' hB hM Z Z'
  have h1 : 0 < 1 - rhoB Dw u := sub_pos.2 (rhoOf_lt_one hu' hu)
  have h2 : ∀ la, topDeg U Z' la = topDeg U Z la := fun la => by rw [topDeg, topDeg, hV Z' Z]
  constructor
  · rw [delPrime, h2]
    have hlow := GlobalTheory.T.cuspFormGrowth_le_imageDegree_lowerWeight E H Dw l Xo c r U hU Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0) (even_wtOf u 0)
      (even_wtOf _ 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top) (hB Z) (hM Z)
    rw [hP Z _ hu', ← ENNReal.ofReal_natCast] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hlow
  · rw [delPrime_eq U Z' (vdm_pos hu).ne', mul_div_cancel_left₀ _ h1.ne', h2]
    exact GlobalTheory.DegTop.compDeg_le hP Z hu
end
end
end
