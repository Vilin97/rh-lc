module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMellin
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfold

-- Source module: GroundTheory.AutomorphicForms.GL2.GJGlobalRank

section

@[expose] public section

open Matrix

namespace GroundTheory.Automorphic

namespace GJGlobal

variable {K : Type*} [Field K] {n : ℕ}

theorem rank_eq_iff_isUnit_det (ξ : Matrix (Fin n) (Fin n) K) : ξ.rank = n ↔ IsUnit ξ.det := by
  constructor
  · intro h
    rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    have hs : Function.Surjective ξ.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact (Matrix.finrank_range_mulVecLin ξ).trans h
    exact LinearMap.injective_iff_surjective.2 hs
  · intro h
    have := rank_of_isUnit ξ ((isUnit_iff_isUnit_det ξ).2 h)
    rwa [Fintype.card_fin] at this

theorem rank_lt_of_det_eq_zero {ξ : Matrix (Fin n) (Fin n) K} (h : ξ.det = 0) : ξ.rank < n := by
  have hle : ξ.rank ≤ n := by
    have := rank_le_card_width ξ
    rwa [Fintype.card_fin] at this
  refine lt_of_le_of_ne hle fun he => ?_
  have := (rank_eq_iff_isUnit_det ξ).1 he
  rw [h] at this
  exact not_isUnit_zero this

theorem rank_eq_zero_iff {ξ : Matrix (Fin n) (Fin n) K} : ξ.rank = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range ξ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 ((Matrix.finrank_range_mulVecLin ξ).trans h)
    have hz : ξ.mulVecLin = 0 := LinearMap.range_eq_bot.1 hr
    ext i j
    have := congrFun (congrArg DFunLike.coe hz) (Pi.single j 1)
    simpa [mulVecLin_apply, mulVec_single_one] using congrFun this i
  · rintro rfl
    exact rank_zero

noncomputable def unitsEquiv : GL (Fin n) K ≃ {ξ : Matrix (Fin n) (Fin n) K // IsUnit ξ.det} where
  toFun γ := ⟨γ, (isUnit_iff_isUnit_det _).1 γ.isUnit⟩
  invFun ξ := ((isUnit_iff_isUnit_det _).2 ξ.2).unit
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem tsum_eq_tsum_GL_add {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ, f ξ = ∑' γ : GL (Fin n) K, f γ + ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {ξ | IsUnit ξ.det}]
  congr 1
  · exact ((unitsEquiv (K := K) (n := n)).tsum_eq (fun ξ => f ξ)).symm
  · have e : ({ξ | IsUnit ξ.det}ᶜ : Set (Matrix (Fin n) (Fin n) K)) = {ξ | ξ.det = 0} := by
      ext ξ
      simp [isUnit_iff_ne_zero]
    rw [e]
    rfl

theorem tsum_det_eq_zero_eq_sum_rank {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ =
      ∑ r : Fin n, ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, f ξ := by
  have e : {ξ : Matrix (Fin n) (Fin n) K | ξ.det = 0} =
      ⋃ r ∈ (Finset.univ : Finset (Fin n)), {ξ | ξ.rank = (r : ℕ)} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨ξ.rank, rank_lt_of_det_eq_zero h⟩, rfl⟩
    · rintro ⟨r, hr⟩
      by_contra h
      have := (rank_eq_iff_isUnit_det ξ).2 (isUnit_iff_ne_zero.2 h)
      have hr' := r.2
      omega
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Disjoint fun r : Fin n => {ξ : Matrix (Fin n) (Fin n) K | ξ.rank = (r : ℕ)}) := by
    intro r _ r' _ hrr'
    refine Set.disjoint_left.2 fun ξ h h' => hrr' (Fin.ext ?_)
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hsum := hasSum_sum_disjoint (f := f) Finset.univ hd fun r _ => (hf.subtype _).hasSum
  show ∑' ξ : ({ξ | ξ.det = 0} : Set (Matrix (Fin n) (Fin n) K)), f ξ = _
  rw [e]
  exact hsum.tsum_eq

end GJGlobal

end GroundTheory.Automorphic
end
end

-- Source module: GroundTheory.AutomorphicForms.GL2.GJGlobalSingular

section

@[expose] public section

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne (K := K) (n := n)

theorem isLeftInvariant_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant ψ) :
    IsLeftInvariant (fun g => conj (ψ g)) := fun γ g => by
  simp only [h γ g]

theorem isCuspidal_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsCuspidal ψ) :
    IsCuspidal (fun g => conj (ψ g)) := by
  intro r hr hrn g
  have := h r hr hrn g
  unfold constantTerm at this ⊢
  rw [integral_conj, this, map_zero]

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem integrableOn_mul_tsum_comp {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    {C : ℝ} (hC : ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C)
    {ι : Type*} [Countable ι] (e : ι → Matrix (Fin n) (Fin n) K) (he : Function.Injective e) :
    IntegrableOn (fun g : normOneGL (K := K) (n := n) => ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' i, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (e i) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])))
      (fundamentalDomain Γ₁) μ := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  refine Measure.integrableOn_of_bounded (M := C) hF.ne ?_ ?_
  · refine ((hψc.comp continuous_subtype_val).measurable.mul ?_).aestronglyMeasurable
    refine UnfoldGL.measurable_tsum_of_summable (fun i => ?_) fun g => ?_
    · exact (hΦ.comp (continuous_const.mul (Units.continuous_val.comp
        continuous_subtype_val))).measurable
    · exact ((hsum g).comp_injective he).of_norm
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hC g g.2)
    refine (norm_tsum_le_tsum_norm ((hsum g).comp_injective he)).trans ?_
    exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
      ((hsum g).comp_injective he) (hsum g)



theorem setIntegral_mul_tsum_det_eq_zero (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hbd
  have hsplit : ∀ g : normOneGL (K := K) (n := n),
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
        ∑ r : Fin n, ψ (g : AdelicGLn.AdelicGL K n) *
          ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
            Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
              ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_det_eq_zero_eq_sum_rank (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, Finset.mul_sum]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_finsetSum _ fun r _ =>
      integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (r : ℕ) = 0
  ·
    have hmem : (0 : Matrix (Fin n) (Fin n) K).rank = r := by rw [Matrix.rank_zero, hr]
    have h0 : ∀ g : normOneGL (K := K) (n := n),
        ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
          Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) = Φ 0 := by
      intro g
      have hu : ∀ ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, ξ = ⟨0, hmem⟩ := by
        intro ξ
        refine Subtype.ext ?_
        have h1 : (ξ : Matrix (Fin n) (Fin n) K).rank = 0 := ξ.2.trans hr
        exact (rank_eq_zero_iff (K := K) (n := n)).1 h1
      rw [tsum_eq_single (⟨0, hmem⟩ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r})
        fun ξ hξ => absurd (hu ξ) hξ]
      have hz : ratMat (0 : Matrix (Fin n) (Fin n) K) = 0 := by
        unfold ratMat
        exact Matrix.map_zero _ (map_zero _)
      rw [hz, mul_zero, zero_mul]
    have hm := setIntegral_fundamentalDomain_eq_zero μ hn hψc hψl hψ hψb
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => by rw [h0 g],
      integral_mul_const, hm, zero_mul]
  ·
    have hk : 0 < n - (r : ℕ) := Nat.sub_pos_of_lt r.2
    have hkn : n - (r : ℕ) < n := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero hr)
    have e : n - (n - (r : ℕ)) = r := Nat.sub_sub_self r.2.le
    have := UnfoldGL.setIntegral_mul_tsum_rank_eq_zero μ hψc hψl hψ hΦ y hsum ⟨C, hC⟩ hk hkn
    rw [e] at this
    exact this



theorem setIntegral_mul_tsum_eq_tsum_GL (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ =
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ := by
  obtain ⟨C, hC⟩ := hbd
  have hsing := setIntegral_mul_tsum_det_eq_zero μ hn hψc hψl hψ hψb hΦ y hsum ⟨C, hC⟩
  have hsplit : ∀ g : normOneGL (K := K) (n := n), ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) +
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_eq_tsum_GL_add (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, mul_add]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_add (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Units.val_injective)
      (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective), hsing, add_zero]

end GJGlobal

end

end GroundTheory.Automorphic
end
end
