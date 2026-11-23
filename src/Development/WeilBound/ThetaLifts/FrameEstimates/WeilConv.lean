module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSum
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.FrameEstimates.ExistsColsDetNeZero
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.FrameBasis
public import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
public import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
public import Development.WeilBound.ThetaLifts.FrameEstimates.HermitianFormDetNeZero
public import Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.SquareIntegrableIntegralHolds
public import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.TriplePairHolds
public import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatArch
import Development.WeilBound.ThetaLifts.FrameEstimates.LatCpt
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
public import Development.WeilBound.ThetaLifts.FrameEstimates.LatTor
public import Development.WeilBound.ThetaLifts.FrameEstimates.OneVar
public import Development.WeilBound.ThetaLifts.FrameEstimates.Parity
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.ThetaLifts.FrameEstimates.SoSemi
public import Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThetaSumNeg

-- Source module: Development.WeilBound.ThetaLifts.FrameEstimates.DomWeil

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domWeilU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqAll) (hI : LatInv) (hM : LatMeas) (hK : LatCpt)
    (hA : LatArch) (hL : LatTor) (hP : PosWt) (h2 : ConeIntegralsFinite) : DomWeilU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hw
  have hc := hp.base.cm
  obtain ⟨hJ, -, hr⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, -, hint, -⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, -, -, -⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg'
  obtain ⟨k, hk⟩ := latSum_redH hT hS hI hK hA hc B.emb hJ hJ' N
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C', K, hC', hK0, hb'⟩ := hk C hC
  obtain ⟨K₀, Ω, hK₀, hΩ, hi⟩ := hint M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω {1} hΩ isCompact_singleton C' N hC'
  obtain ⟨K₂, h₂'⟩ := hN C₁ hC₁
  have ha0 : fr'.a 0 = 1 := by
    have := hg'.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h0 : (0 : Fin fr'.r → ℝ) ∈ Cone fr'.r := ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hmeas : Measurable fun g : UA σ X.J => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ) :=
    (hM F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ hC' 1).pow_const _
  set D : ℝ := (Module.finrank ℚ E : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  refine ⟨NNReal.mk K hK0 • p, fun g => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ), ?_, hmeas, ?_, ?_⟩
  · exact (continuous_const.mul hpc : Continuous fun f => K * p f)
  · have hq : fr.r = 0 ∨ d + 2 * fr.r < 2 * n := by
      have := hr fr hg
      omega
    have hfin := (h2 n d fr.r 0 D hD0 hq (Or.inl rfl)).1
    set c : ℝ≥0∞ := ((K₁ : ℝ≥0∞) * K₂) ^ (1 / 2 : ℝ) with hcdef
    have hcfin : c < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have key := hi (fun t => c * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i)))) (by fun_prop) _ hmeas
      (fun γ hγ g => by
        have := hI F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ (by simp) γ hγ 1 (one_mem _) g 1
        rw [mul_one] at this
        rw [this])
      (fun t ht' κ hκ => by
        have e1 := h₁ Set.univ (fr.a t) 1 κ hκ 1 rfl
        rw [mul_one] at e1
        have e2 := h₂' t ht' 0 h0
        rw [ha0] at e2
        have e3 : posWt n d t (0 : Fin fr'.r → ℝ) ≤ d * ∑ i, t i := by
          simpa using (hP n d fr.r fr'.r t 0 ht' h0).1
        have e4 : latSum B.emb C' N Set.univ (fr.a t * κ) (1 : UA σ W.J) ≤
            ((K₁ : ℝ≥0∞) * K₂) * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i))) ^ (2 : ℝ) := by
          refine e1.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_right (e2.trans (mul_le_mul_right ?_ _)) _
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          nlinarith
        refine (ENNReal.rpow_le_rpow e4 (by norm_num)).trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hcdef])
    refine key.trans_lt (ENNReal.mul_lt_top hK₀ ?_)
    simp only [mul_assoc c]
    rw [lintegral_const_mul' _ _ hcfin.ne]
    exact ENNReal.mul_lt_top hcfin hfin
  · intro f g h
    have e := (hb f g h).trans (mul_le_mul_right (hb' g h) _)
    have hpf : 0 ≤ p f := apply_nonneg p f
    have e2 : ‖theta om (pureA F f φ) g h‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (K * p f * (ht h : ℝ) ^ k) ^ (2 : ℝ) * latSum B.emb C' N Set.univ g (1 : UA σ W.J) := by
      rw [ENNReal.rpow_two, ENNReal.rpow_two]
      refine e.trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      congr 2
      ring
    have e3 := ENNReal.rpow_le_rpow e2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at e3
    norm_num at e3
    simpa [NNReal.smul_def] using e3

end PositivityTheory.ThKEst

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.FrameEstimates.IContOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iCont_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hW : DomWeil) (hS : DomSoU) (hF : SoFin) :
    PositivityTheory.ThKF.ICont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine ⟨fun hw Φ hΦ => ?_, fun _ Φ hΦ => ?_⟩
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.1 Φ hΦ
    have hd := hW F E σ B n d X W M χX χW om r s r' s' hp hw
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ hφ).2.2]
    exact continuous_finsetSum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i) (f i)
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
    have hd := dom_of_domSoU hS hp
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ fun i => (hφ i).1).2.2]
    exact continuous_finsetSum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i).1 (f i)

end PositivityTheory.ThKEst

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.FrameEstimates.LatFull

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.FrameEstimates.LatInv

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def latInvEquiv {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) :
    Matrix (Fin n) (Fin d) E ≃ Matrix (Fin n) (Fin d) E where
  toFun x := a.1 * x * b.1ᵀ
  invFun x := (a⁻¹).1 * x * (b⁻¹).1ᵀ
  left_inv x := by
    have h1 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
    have h2 : b.1ᵀ * (b⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show (b⁻¹).1 * b.1 = 1 from b.inv_mul, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  right_inv x := by
    have h1 : a.1 * (a⁻¹).1 = 1 := a.mul_inv
    have h2 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show b.1 * (b⁻¹).1 = 1 from b.mul_inv, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem latInvEquiv_rank {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E)
    (x : Matrix (Fin n) (Fin d) E) : (latInvEquiv a b x).rank = x.rank := by
  have ha : IsUnit a.1.det := (Matrix.isUnit_iff_isUnit_det _).1 a.isUnit
  have hb : IsUnit b.1ᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  change (a.1 * x * b.1ᵀ).rank = x.rank
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hb, Matrix.rank_mul_eq_right_of_isUnit_det _ _ ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latInv_mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (hγ : γ ∈ ratU σ J) :
    ∃ a : GL (Fin n) E, ∀ g : UA σ J, mat (γ * g)⁻¹ = mat g⁻¹ * incM F a.1 := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 ((ratU σ J).inv_mem hγ)
  refine ⟨a, fun g => ?_⟩
  have h1 : mat γ⁻¹ = incM F a.1 := (congrArg Units.val ha).symm
  rw [mul_inv_rev, ← h1]
  rfl

theorem latInv_incM {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) (x : Matrix (Fin n) (Fin d) E) :
    incM F (latInvEquiv a b x) = incM F a.1 * incM F x * (incM F b.1)ᵀ := by
  change incM F (a.1 * x * b.1ᵀ) = _
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

theorem latInv_of : LatInv := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hS γ hγ δ hδ g h
  obtain ⟨a, ha⟩ := latInv_mat_inv_mul γ hγ
  obtain ⟨b, hb⟩ := latInv_mat_inv_mul δ hδ
  have hSS : ∀ x, x ∈ S ↔ latInvEquiv a b x ∈ S := by
    intro x
    rcases hS with rfl | rfl
    · simp
    · simp only [fullRank, Set.mem_setOf_eq, latInvEquiv_rank]
  unfold latSum
  rw [← Equiv.tsum_eq ((latInvEquiv a b).subtypeEquiv hSS)
    (fun x : S => ENNReal.ofReal (maj τ C N (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ)))]
  refine tsum_congr fun x => ?_
  rw [Equiv.subtypeEquiv_apply, ha, hb, latInv_incM, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end PositivityTheory.ThKEst

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sqAll : SqAll := sqAll_of' coefSum coefEq_of (coefBd_of coefReal_of)

theorem sqSo : SqSo :=
  sqSo_of' soFin_of soCut_of (parity_of coefEq_of fourierInj_of) coefSum coefEq_of (coefBd_of coefReal_of)

theorem latTor : LatTor := latTor_of frameBasis_of oneVar_of

theorem latFull : LatFull := latFull_of latTor (minor_of frameBasis_of)

theorem domWeilU (h : GlobalTheory.Published.SiegelSetUnitary) : DomWeilU :=
  domWeilU_of grpTop_of epsOf_of (siegelAll_of h) sqAll latInv_of latMeas latCpt_of (latArch_of frameBasis_of) latTor
    Sq.posWt' Sq.square_integrable_integral_holds

theorem soSemiU (h : GlobalTheory.Published.SiegelSetUnitary) : SoSemiU :=
  soSemiU_of grpTop_of epsOf_of (siegelAll_of h) sqSo latInv_of latCpt_of latFull Sq.posWt'

theorem domSoU (h : GlobalTheory.Published.SiegelSetUnitary) : DomSoU := domSoU_of epsOf_of finVolU (soSemiU h)

theorem weilConv (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : WeilConv :=
  weilConv_of hB (domWeil_of_U (domWeilU h)) soFin_of

theorem soDecay (h : GlobalTheory.Published.SiegelSetUnitary) : SoDecay := soDecay_of (soSemi_of_U (soSemiU h)) soFin_of

theorem soCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : SoCont := soCont_of hB (domSoU h) soFin_of

theorem kDecay (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : KDecay :=
  kDecay_of hB Sq.triplePair_holds (weilConv h hB) (soDecay h) (domSoU h) soFin_of

theorem iCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : PositivityTheory.ThKF.ICont :=
  iCont_of hB grpTop_of epsOf_of (domWeil_of_U (domWeilU h)) (domSoU h) soFin_of

end PositivityTheory.ThKEst

end
end
end
