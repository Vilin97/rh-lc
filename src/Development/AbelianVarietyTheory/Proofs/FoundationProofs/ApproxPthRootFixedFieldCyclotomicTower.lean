module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTowerStatement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPow

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] (v : Valuation L ℝ≥0) {p : ℕ} {θ : ℝ≥0}

theorem approxRoot_pow_le (hθ : θ ≤ 1) {u w : L} (h : v (u - w ^ p) ≤ θ * v u) :
    v (w ^ p) ≤ v u := by
  have e : w ^ p = u - (u - w ^ p) := by ring
  rw [e]
  refine (Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))
  simpa using mul_le_mul' hθ (le_refl (v u))

theorem approxRoot_mul (hθ : θ ≤ 1) {u u' w w' : L} (h : v (u - w ^ p) ≤ θ * v u)
    (h' : v (u' - w' ^ p) ≤ θ * v u') : v (u * u' - (w * w') ^ p) ≤ θ * v (u * u') := by
  have e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p) := by ring
  rw [e, map_mul]
  refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v u * v (u' - w' ^ p) ≤ v u * (θ * v u') := mul_le_mul' le_rfl h'
      _ = θ * (v u * v u') := by ring
  · rw [map_mul]
    calc v (w' ^ p) * v (u - w ^ p) ≤ v u' * (θ * v u) :=
          mul_le_mul' (approxRoot_pow_le v hθ h') h
      _ = θ * (v u * v u') := by ring

theorem approxRoot_inv (hθ : θ < 1) {u w : L} (hu : u ≠ 0) (h : v (u - w ^ p) ≤ θ * v u) :
    v (u⁻¹ - (w⁻¹) ^ p) ≤ θ * v u⁻¹ := by
  have hvu : 0 < v u := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff v).mpr hu
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)
  have heq : v (w ^ p) = v u := Valuation.map_eq_of_sub_lt v hlt
  have hw : w ^ p ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact hvu.ne' heq.symm
  have e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹) := by
    rw [inv_pow]; field_simp
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]
  calc v (u - w ^ p) * ((v u)⁻¹ * (v u)⁻¹) ≤ θ * v u * ((v u)⁻¹ * (v u)⁻¹) :=
        mul_le_mul' h le_rfl
    _ = θ * (v u)⁻¹ := by field_simp

theorem approxRoot_closed : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  intro L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩
  have hθ1 : θ ≤ 1 := hθ.le
  refine ⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩
  · refine ⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩
    rw [div_eq_mul_inv]
    exact approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')
  · induction k with
    | zero => exact ⟨1, F.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨x, hxF, hx⟩ := ih
      refine ⟨x * w, F.mul_mem hxF hwF, ?_⟩
      rw [pow_succ]
      exact approxRoot_mul v hθ1 hx hw

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPowStatement

section

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.approxPthRoot_closed_mul_div_pow : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_closed | exact GlobalTheory.AlmostEt.approxRoot_closed | (intros; apply GlobalTheory.AlmostEt.approxRoot_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoinStatement

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧ ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.K5.exists_level_of_mem_adjoin | exact GlobalTheory.K5.exists_level_of_mem_adjoin | (intros; apply GlobalTheory.K5.exists_level_of_mem_adjoin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevelStatement

section

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n → ∃ _ : IsDomain (On p n), IsDiscreteValuationRing (On p n) ∧ Irreducible (xn p n - 1) := by
  first | exact @GlobalTheory.K5.OnDVR.isDVR_On | exact GlobalTheory.K5.OnDVR.isDVR_On | (intros; apply GlobalTheory.K5.OnDVR.isDVR_On <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizer

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.UnitPow

theorem eq_unit_mul_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  intro p _ Ω _ _ hclo T b hb hb0
  obtain ⟨n, ι, w, hn, hemb, hw, hmem⟩ := GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq p Ω hclo T b hb
  obtain ⟨hdom, hdvr, hirr⟩ := GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel p n hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hw, map_zero])
  obtain ⟨k, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hirr
  refine ⟨n, k, hn, ι (ε : On p n), hmem _, ι ((ε⁻¹ : (On p n)ˣ) : On p n), hmem _, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← hw, hε, map_mul, map_pow, map_sub, map_one, hemb.1]

end GlobalTheory.K5.UnitPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizerStatement

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  first | exact @GlobalTheory.K5.UnitPow.eq_unit_mul_pow | exact GlobalTheory.K5.UnitPow.eq_unit_mul_pow | (intros; apply GlobalTheory.K5.UnitPow.eq_unit_mul_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixedStatement

section

@[expose] public section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_div_mem_adjoin_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  first | exact @GlobalTheory.mem_adjoin_div_of_fixed | exact GlobalTheory.mem_adjoin_div_of_fixed | (intros; apply GlobalTheory.mem_adjoin_div_of_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTower

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TopRoots

theorem approxRoot_fix_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0),
    (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
    0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  intro p _ Ω _ _ hp2 hclo T v hv _ hp1
  classical
  have hpp : p.Prime := Fact.out
  let S : Set Ω := Set.range T.ζ ∪ Set.range T.qq
  let B := Algebra.adjoin (O0 p) S
  let F := Fix Ω (⨅ n, Gn T n)

  have hBle : B ≤ integralClosure (O0 p) Ω := by
    rw [Algebra.adjoin_le_iff]
    rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [(T.prim n).pow_eq_one]; exact isIntegral_one
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [Basic.qq_pow]; exact isIntegral_algebraMap
  have hBint : ∀ x ∈ B, v x ≤ 1 := fun x hx => (hv x).2 (hBle hx)

  have hBF : ∀ x ∈ B, x ∈ F := by
    intro x hx g
    have hg : (g : Gal p Ω) ∈ ⨅ n, Gn T n := g.2
    rw [Subgroup.mem_iInf] at hg
    have hle : B ≤ AlgHom.equalizer (g : Gal p Ω).toAlgHom (AlgHom.id (O0 p) Ω) := by
      rw [Algebra.adjoin_le_iff]
      rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · exact ((Basic.mem_gn T n _).1 (hg n)).1
      · exact ((Basic.mem_gn T n _).1 (hg n)).2
    have := hle hx
    rw [AlgHom.mem_equalizer] at this
    exact this

  set θ := v (T.ζ 1 - 1) with hθ
  have hz1 := GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 1 le_rfl
  have hθ1 : θ < 1 := hz1.1
  let good : Ω → Prop := fun x => ∃ w ∈ F, v (x - w ^ p) ≤ θ * v x

  have hgoodB : ∀ x ∈ B, v (p : Ω) ≤ θ * v x → good x := by
    intro x hx hvx
    obtain ⟨y, hy, z, hz, e⟩ := GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower p Ω T x hx
    refine ⟨y, hBF y hy, ?_⟩
    have : x - y ^ p = (p : Ω) * z := by rw [e]; ring
    rw [this, map_mul]
    calc v (p : Ω) * v z ≤ v (p : Ω) * 1 := mul_le_mul_of_nonneg_left (hBint z hz) zero_le
      _ = v (p : Ω) := mul_one _
      _ ≤ θ * v x := hvx

  have hunit : ∀ u ∈ B, ∀ u' ∈ B, u * u' = 1 → good u := by
    intro u hu u' hu' e
    have hvu : v u = 1 := by
      have h1 := hBint u hu
      have h2 := hBint u' hu'
      have h3 : v u * v u' = 1 := by rw [← map_mul, e, map_one]
      by_contra hne
      have hlt : v u < 1 := lt_of_le_of_ne h1 hne
      have : v u * v u' < 1 := by
        calc v u * v u' ≤ v u * 1 := mul_le_mul_of_nonneg_left h2 zero_le
          _ = v u := mul_one _
          _ < 1 := hlt
      exact absurd h3 (ne_of_lt this)
    refine hgoodB u hu ?_
    rw [hvu, mul_one]
    calc v (p : Ω) ≤ θ * v (T.ζ 1 - 1) := hz1.2
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hθ1.le zero_le
      _ = θ := mul_one _

  have hzeta : ∀ n, 1 ≤ n → good (T.ζ n - 1) := by
    intro n hn
    have hmem : T.ζ n - 1 ∈ B :=
      Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)) (Subalgebra.one_mem _)
    exact hgoodB _ hmem (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 n hn).2

  have hB : ∀ b ∈ B, good b := by
    intro b hb
    by_cases hb0 : b = 0
    · refine ⟨0, F.zero_mem, ?_⟩
      rw [hb0, zero_pow hpp.ne_zero, sub_zero, map_zero]; exact zero_le
    obtain ⟨n, k, hn, u, hu, u', hu', e, rfl⟩ := GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer p Ω hclo T b hb hb0
    have h1 := hunit u hu u' hu' e
    have h2 := (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hzeta n hn) (hzeta n hn)).2.2 k
    exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ h1 h2).1

  refine ⟨θ, hθ1, fun x hx => ?_⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hclo
  haveI : IsAlgClosed Ω := hclo.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hclo.alg
  have hfix : ∀ g : Ω ≃ₐ[O0 p] Ω, (∀ s ∈ S, g s = s) → g x = x := by
    intro g hg
    have hgm : g ∈ ⨅ n, Gn T n := by
      rw [Subgroup.mem_iInf]
      intro n
      exact (Basic.mem_gn T n g).2
        ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩
    exact hx ⟨g, hgm⟩
  obtain ⟨b, hb, c, hc, hc0, rfl⟩ := GlobalTheory.T.exists_div_mem_adjoin_of_fixed (O0 p) Ω hclo.inj S x hfix
  exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hB b hb) (hB c hc)).2.1 hc0

end GlobalTheory.K5.TopRoots
end
end
