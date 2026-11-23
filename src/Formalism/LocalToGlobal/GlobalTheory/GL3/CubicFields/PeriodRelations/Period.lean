module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.FractionalIdealDualFamily
public import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.MapMulLeftDenSpanImageEqMapNum
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.NormSum
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LiftMOneExt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem liftM_val_ext {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  simp [liftM, h]

theorem liftM_mul_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a * b)) = liftM M (σ a) * liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a * b)), IntermediateField.coe_mul, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_mul]

theorem liftM_add_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a + b)) = liftM M (σ a) + liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a + b)), IntermediateField.coe_add, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_add]

theorem liftM_one_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) :
    liftM M (σ 1) = 1 := by
  apply Subtype.ext
  rw [map_one, liftM_val_ext (one_mem M), IntermediateField.coe_one]

theorem liftM_int_ext {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (e : 𝓞 E) :
    liftM M (σ (algebraMap (𝓞 E) E e)) ∈ (algebraMap (𝓞 M) M).range := by
  have h1 : IsIntegral ℤ (σ (algebraMap (𝓞 E) E e)) :=
    (RingOfIntegers.isIntegral_coe e).map σ.toIntAlgHom
  have hx : IsIntegral ℤ (liftM M (σ (algebraMap (𝓞 E) E e))) := by
    rw [← isIntegral_algHom_iff (algebraMap M ℂ).toIntAlgHom (algebraMap M ℂ).injective]
    change IsIntegral ℤ ((liftM M (σ (algebraMap (𝓞 E) E e)) : M) : ℂ)
    rwa [liftM_val_ext (hσ _)]
  exact ⟨⟨_, hx⟩, rfl⟩

theorem mem_imI_iff {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (x : M) :
    x ∈ imI M σ J ↔
      ∀ b ∈ ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), x * liftM M (σ b) ∈ (algebraMap (𝓞 M) M).range := by
  have hJJ : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have hint : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E), liftM M (σ z) ∈ (algebraMap (𝓞 M) M).range := by
    intro z hz
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one] at hz
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
    exact liftM_int_ext M σ hσ y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro b hb
      rw [← liftM_mul_ext M σ hσ]
      exact hint _ (Submodule.mul_mem_mul ha hb)
    | zero =>
      intro b _
      rw [zero_mul]
      exact zero_mem _
    | add y z _ _ hy hz =>
      intro b hb
      rw [add_mul]
      exact add_mem (hy b hb) (hz b hb)
    | smul r y _ hy =>
      intro b hb
      rw [smul_mul_assoc, Algebra.smul_def]
      exact mul_mem (RingHom.mem_range_self _ r) (hy b hb)
  · intro hx
    have key : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
        Submodule (𝓞 E) E), x * liftM M (σ z) ∈ imI M σ J := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        obtain ⟨r, hr⟩ := hx b hb
        rw [liftM_mul_ext M σ hσ, mul_comm (liftM M (σ a)), ← mul_assoc, ← hr, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a, ha, rfl⟩)
      | add y _ z _ hy hz =>
        rw [liftM_add_ext M σ hσ, mul_add]
        exact add_mem hy hz
    have := key 1 hJJ
    rwa [liftM_one_ext, mul_one] at this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.CoeIdealDifferentNeZero

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem dual_eq_inv_mul_different (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
  rw [coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E), FractionalIdeal.dual_eq_mul_inv (𝓞 K) K I, mul_inv,
    inv_inv, mul_comm]

theorem coeIdeal_different_ne_zero (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E] :
    ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
  rw [coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero (𝓞 K) K one_ne_zero)

theorem lineR_eq (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) :
    lineR M emb I i = imI M (emb i) (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) := by
  have h0 : liftM M 0 = 0 := by
    rw [liftM, dite_eq_left (zero_mem M)]
    rfl
  by_cases hI : I = 0
  · subst hI
    rw [zero_mul]
    have hm : mmR M emb (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [mmR, Submodule.span_eq_bot]
      rintro v ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      funext k
      simp [h0]
    have hR : imI M (emb i) (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [imI, Submodule.span_eq_bot]
      rintro y ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      simp [h0]
    rw [hR, lineR, hm]
    ext x
    simp
  · have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
      mul_ne_zero hI (coeIdeal_different_ne_zero K E)
    ext x
    rw [lineR, Submodule.mem_comap, mem_mmR_iff K E φ₀ M ι emb hinj hres hcard hM I hI,
      mem_imI_iff M (emb i) (hM i) _ hJ, ← dual_eq_inv_mul_different K E I]
    refine forall₂_congr fun b _ => ?_
    simp [Pi.single_apply]

theorem index_lineR (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (i : ι) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ lineR M emb I i) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M emb I i).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) : ℚ) : ℝ) ^
        Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    mul_ne_zero hI (coeIdeal_different_ne_zero K E)
  have heq := lineR_eq K E φ₀ M ι emb hinj hres hcard hM I i
  rw [heq] at hs ⊢
  exact index_imI M (emb i) (hM i) _ hJ s hs0 hs

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Period

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_ellT_eq (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Formalism.MainNotions.TaylorLogMetric.ellT D M τ = lineR M (embT D) D.host.AA0 τ := rfl

theorem br_brN_eq (D : D7) : brN D = ((FractionalIdeal.absNorm (D.host.AA0 *
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) := rfl

theorem br_exists_ellT (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) :
    ∃ s : M, s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := by
  rw [br_ellT_eq, lineR_eq D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb]
  have hJ : D.host.AA0 * ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    mul_ne_zero (leading_constant_ne_zero D) (coeIdeal_different_ne_zero _ _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine ⟨liftM M (embT D τ a), ?_, Submodule.subset_span ⟨a, ha, rfl⟩⟩
  have hm := hemb τ a
  unfold liftM
  rw [dite_eq_left hm]
  intro h
  have : embT D τ a = 0 := congrArg Subtype.val h
  exact ha0 ((map_eq_zero (embT D τ)).mp this)

theorem br_meanLogOm_eq (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau)
    (hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) :
    meanLogOm D Λ M τ =
      -(2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) +
        (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi)) /
          (Module.finrank ℚ M : ℝ) := by
  have hex := br_exists_ellT D M hemb τ
  unfold meanLogOm
  dsimp only
  set s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ) with hsdef
  have hs : s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := Classical.epsilon_spec hex
  rw [br_ellT_eq] at hs ⊢
  have hidx := index_lineR D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb D.host.AA0 (leading_constant_ne_zero D) τ s hs.1 hs.2
  rw [← br_brN_eq] at hidx
  set x : ℝ := ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M (embT D) D.host.AA0 τ).toAddSubgroup).index : ℕ) : ℝ) with hxdef
  set e : ℕ := Module.finrank ℚ D.host.E with he
  set m : ℕ := Module.finrank ℚ M with hm
  set ns : ℝ := |((Algebra.norm ℚ s : ℚ) : ℝ)| with hns
  have hns0 : ns ≠ 0 := by
    rw [hns, abs_ne_zero, Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hs.1
  have hrhs : ns ^ e ≠ 0 := pow_ne_zero _ hns0
  have hl : x ^ e * brN D ^ m ≠ 0 := hidx ▸ hrhs
  have hx0 : x ^ e ≠ 0 := left_ne_zero_of_mul hl
  have hN0 : brN D ^ m ≠ 0 := right_ne_zero_of_mul hl
  have hlog : (e : ℝ) * Real.log x + (m : ℝ) * Real.log (brN D) = (e : ℝ) * Real.log ns := by
    have := congrArg Real.log hidx
    rw [Real.log_mul hx0 hN0, Real.log_pow, Real.log_pow, Real.log_pow] at this
    exact this
  have he0 : (e : ℝ) ≠ 0 := by
    rw [he]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.host.E).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    rw [hm]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ M).ne'
  have hterm : ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      Real.log Real.pi + Real.log (‖ρ s‖ ^ 2) - Real.log (area (lamConj M ρ Λ)) := by
    intro ρ
    unfold Formalism.MainNotions.TaylorLogMetric.logMet
    rw [br_area_eq]
    have hρ : ‖ρ s‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero ρ).mpr hs.1))
    rw [Real.log_div (mul_ne_zero Real.pi_ne_zero hρ) (hpos ρ).ne', Real.log_mul Real.pi_ne_zero hρ]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      (m : ℝ) * Real.log Real.pi + 2 * Real.log ns -
        ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) := by
    rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      br_sum_log_norm_sq M s hs.1, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  have hsum2 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi) =
      ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) - (m : ℝ) * Real.log Real.pi := by
    rw [Finset.sum_congr rfl (fun ρ _ => Real.log_div (hpos ρ).ne' Real.pi_ne_zero),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  rw [hsum, hsum2]
  field_simp
  linear_combination 2 * hlog

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end
end
