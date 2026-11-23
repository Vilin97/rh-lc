module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMemStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
        (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) →
        ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
          (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
          ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
            (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t →
            ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  let : Algebra ℤ_[p] Ω := zpAlg (p := p) (Ω := Ω)
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hAlg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsmul (c : ℤ_[p]) (x : Ω) : c • x = zp Ω c * x := by
    rw [Algebra.smul_def]
    congr 1
    change algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) c) = zp Ω c
    rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hxInt, hxS⟩ ⟨hyInt, hyS⟩
        exact ⟨IsIntegral.add hxInt hyInt, by rw [mul_add]; exact S.add_mem hxS hyS⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hxInt, hxS⟩
        refine ⟨?_, ?_⟩
        · change IsIntegral (O0 p) (c • x)
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hxInt
        · change (p : Ω) ^ v * (c • x) ∈ S
          rw [mul_smul_comm]
          exact S.smul_mem c hxS }
  let U := Submodule.span ℤ_[p] (Set.range fun t => E t / (p : Ω) ^ v)
  have hle : S' ≤ U := by
    rintro y ⟨_, hy⟩
    change (p : Ω) ^ v * y ∈ Submodule.span ℤ_[p] (Set.range E) at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    apply (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2
    refine ⟨c, ?_⟩
    calc
      ∑ t, c t • (E t / (p : Ω) ^ v) = (∑ t, c t • E t) / (p : Ω) ^ v := by
        simp only [Finset.sum_div, smul_div_assoc]
      _ = y := (div_eq_iff hpv).2 (hc.trans (mul_comm _ _))
  have hnoeth : IsNoetherian ℤ_[p] U :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem (j : Fin m) : IsInt (p := p) (f j) ∧ (p : Ω) ^ v * f j ∈ S := by
    change f j ∈ S'
    rw [← hf]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hAlgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    change x ∈ Submodule.span ℤ_[p] (Set.range E) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (hAlg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · apply (hAlg _).2
    have hInv : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) :=
      ((isAlgebraic_natCast p : IsAlgebraic ℤ_[p] (p : Ω)).pow v).inv
    have h := hInv.mul (hAlgS _ (hfmem j).2)
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at h
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsmul]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by simpa only [hsmul] using hμ.symm⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEval

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix.Divide

theorem divide_ev : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o →
    ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  intro p _ Ω _ _ hc T n ψ h d e a he v o ho hsum
  classical
  haveI := Basic.charZero_of_isClo hc
  set c : ℤ → Ω := fun r => ∑ t, e t * zp Ω ((a t).coeff r) with hcdef
  have hev : Ev ψ c (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
      (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) :=
    ⟨d, e, a, he, fun r => rfl, rfl, rfl⟩
  have hcong : Cong (p := p) v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) 0 :=
    ⟨o, ho, by rw [sub_zero, hsum]⟩
  have hcr := ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T n ψ h v c _ _ hev).1.1 hcong)
  choose y hy hcy using hcr
  obtain ⟨m, f, hf, hlat⟩ := GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem p Ω hc d e he v
  have hμ : ∀ r, ∃ μ : Fin m → ℤ_[p], y r = ∑ j, zp Ω (μ j) * f j := by
    intro r
    refine hlat (fun t => (a t).coeff r) (y r) (hy r) ?_
    have := hcy r
    rw [sub_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  choose μ hμ using hμ
  let μ' : ℤ → Fin m → ℤ_[p] := fun r => if ∀ t, (a t).coeff r = 0 then 0 else μ r
  have hsupp : ∀ j, (Function.support fun r => μ' r j) ⊆ ⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support := by
    intro j r hr
    simp only [Function.mem_support] at hr
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · exact absurd (by simp [μ', h0]) hr
    · push_neg at h0
      obtain ⟨t, ht⟩ := h0
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ t)) ht
  have hpwo : (⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support).IsPWO :=
    (Finset.univ.isPWO_bUnion).2 fun t _ => (a t).isPWO_support
  let Λ : Fin m → Lau p := fun j => ⟨fun r => μ' r j, hpwo.mono (hsupp j)⟩
  have hΛ : ∀ j r, (Λ j).coeff r = μ' r j := fun _ _ => rfl

  let Λp : Fin m → Lau p := fun j => HahnSeries.C ((p : ℤ_[p]) ^ v) * Λ j
  have hzpp : zp Ω ((p : ℤ_[p]) ^ v) = (p : Ω) ^ v := by
    rw [← GlobalTheory.EvUniq.zpHom_apply, map_pow, map_natCast]
  have hcoef : ∀ r, c r = ∑ j, f j * zp Ω ((Λp j).coeff r) := by
    intro r
    have hc1 : ∀ j, zp Ω ((Λp j).coeff r) = (p : Ω) ^ v * zp Ω (μ' r j) := by
      intro j
      simp only [Λp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hΛ]
      rw [← GlobalTheory.EvUniq.zpHom_apply, map_mul, GlobalTheory.EvUniq.zpHom_apply, GlobalTheory.EvUniq.zpHom_apply, hzpp]
    simp only [hc1]
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · have hμ0 : μ' r = 0 := by simp [μ', h0]
      have hz : zp Ω (0 : ℤ_[p]) = 0 := by rw [← GlobalTheory.EvUniq.zpHom_apply, map_zero]
      simp [hcdef, h0, hμ0, hz]
    · have hμr : μ' r = μ r := by simp [μ', h0]
      have := hcy r
      rw [sub_zero] at this
      rw [this, hμ r, hμr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hev2 : Ev ψ c (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)))
      (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (thL (Λp j)))) :=
    ⟨m, f, Λp, hf, hcoef, rfl, rfl⟩
  have heq := (GlobalTheory.EvUniq.ev_unique p Ω hc T n ψ h c _ _ _ _ hev hev2).1
  have hval : ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)) =
      (p : Ω) ^ v * ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Λp, map_mul, GlobalTheory.EvUniq.psi_C h, hzpp]
    ring
  have hp0 : (p : Ω) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have ho' : o = ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [hsum, hval] at heq
    exact mul_left_cancel₀ hp0 heq
  exact ⟨fun r => ∑ j, f j * zp Ω ((Λ j).coeff r), _, m, f, Λ, hf, fun r => rfl, ho', rfl⟩

end GlobalTheory.GeoFix.Divide
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEvalStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o → ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  first | exact @GlobalTheory.GeoFix.Divide.divide_ev | exact GlobalTheory.GeoFix.Divide.divide_ev | (intros; apply GlobalTheory.GeoFix.Divide.divide_ev <;> assumption)
end
end
