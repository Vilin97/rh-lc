module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAverageKillsFockComplementRelInvariantsStatement
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinorsStatement

section

@[expose] public section

open Classical

theorem _root_.GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  first | exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors | exact GlobalTheory.MinorFrame.inv_le_span_prodMinors | (intros; apply GlobalTheory.MinorFrame.inv_le_span_prodMinors <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFockProjectionMaximalMinors

section

@[expose] public section

open Classical MeasureTheory

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RatProj

section Form

variable {σ : Type}

def fockQ (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ)

theorem fockQ_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp

def fockQL : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ fockQ
    (by
      intro f f' g
      rw [fockQ_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockQ_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockQ_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_add]; ring)
    (by
      intro c f g
      rw [fockQ_eq_sum (c • f) g f.support support_smul, fockQ, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockQ, MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

theorem fockQL_apply (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl

theorem fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by
  rw [Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem eq_zero_of_fockQ_self {f : MvPolynomial σ ℚ} (h : fockQ f f = 0) : f = 0 := by
  by_contra hf
  have hf' : map (algebraMap ℚ ℂ) f ≠ 0 := by
    intro h0
    apply hf
    exact map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  have := GlobalTheory.MinorFrame.fockS_self_re_pos hf'
  rw [fockS_map, h] at this
  simp at this

end Form

variable {ι : Type} [Fintype ι]

def prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : MvPolynomial (Var ι d a) ℚ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a => (X (τ, (T τ j).1 i, i') : MvPolynomial (Var ι d a) ℚ)).det

theorem map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by
  simp only [prodMinorsQ, prodMinors, minorAt, map_prod]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by

    rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]

end GlobalTheory.MinorFrame.RatProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFockProjectionMaximalMinorsStatement

section

@[expose] public section

open Classical MeasureTheory

theorem _root_.GlobalTheory.T.exists_rational_fock_projection_maximal_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  first | exact @GlobalTheory.MinorFrame.RatProj.exists_rat_proj | exact GlobalTheory.MinorFrame.RatProj.exists_rat_proj | (intros; apply GlobalTheory.MinorFrame.RatProj.exists_rat_proj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZeroStatement

section

@[expose] public section

open Classical MeasureTheory

theorem _root_.GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  first | exact @GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | exact GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | (intros; apply GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinors

section

@[expose] public section

noncomputable section

open Classical MeasureTheory MvPolynomial

namespace GlobalTheory.MinorFrame.AvgCore

variable {ι : Type} [Fintype ι] {a d : ℕ}

theorem continuous_colSub_mul (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) : ∀ Q : Pol ι d a,
    Continuous (fun G : ι → Fin a → Fin a → ℂ => Λ (colSub (fun τ => Matrix.of (G τ)) P * Q)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d := d) (fun τ => Matrix.of (G τ)) (C c) = C c := by
      intro G; simp [colSub, MvPolynomial.algebraMap_eq]
    simp only [h]
    exact continuous_const
  | add p q hp hq =>
    intro Q
    simp only [map_add (f := _), add_mul]
    exact (hp Q).add (hq Q)
  | mul_X p y hp =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) =
        ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q)) := by
      intro G
      have hX : colSub (d := d) (fun τ => Matrix.of (G τ)) (X y) =
          ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by
        simp [colSub]

      rw [map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q =
          C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring,
        ← smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [h]
    refine continuous_finsetSum _ fun j _ => ?_
    exact Continuous.mul (by fun_prop) (hp _)

theorem norm_det_unitary (u : Matrix.unitaryGroup (Fin a) ℂ) : ‖(u : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)

theorem integrable_avg {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hmeas : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (z : ι → ℤ)
    (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) :
    Integrable (fun g => (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (z τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ν := by
  let F : (ι → Fin a → Fin a → ℂ) → ℂ := fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)
  have hF : Continuous F := by simpa [F] using continuous_colSub_mul Λ P 1
  let e : K → (ι → Fin a → Fin a → ℂ) := fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j
  have he : Measurable e := Measurable.of_eval fun τ => Measurable.of_eval fun i =>
    Measurable.of_eval fun j => hmeas τ i j
  have hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g) := fun g => rfl
  have hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det := fun g τ => rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  have hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1 := by
    intro g
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [hFe, hdete]
    refine Measurable.mul ?_ (hF.measurable.comp he)
    refine Finset.measurable_prod _ fun τ _ => ?_
    exact Measurable.pow_const ((hdetc τ).measurable.comp he) _
  · rw [norm_mul, norm_prod]
    simp only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]
    exact hC _ (hball g)

theorem average_monomial_eq_sum_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  intro ι _ a d m
  refine ⟨fun τ => (-m τ).toNat, ?_⟩
  intro K _ _ ν hP hInv hleft ρ hmeas hsurj Λ k
  haveI := hP
  by_cases hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀
  · obtain ⟨ha, τ₀, hτ₀⟩ := hpos
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
    rw [GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv hleft ρ hmeas hsurj Λ _]
    simp
  obtain ⟨M, r, U, hR⟩ := GlobalTheory.T.exists_rational_fock_projection_maximal_minors (ι := ι) a d (fun τ => (-m τ).toNat) k
  refine ⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩
  set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef
  have hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0 := by
    intro I hI
    have hspan := GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI
    clear hI
    show Formalism.L2.DIV.fockL I R = 0
    induction hspan using Submodule.span_induction with
    | mem x hx => obtain ⟨T, rfl⟩ := hx; exact hR T
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
  have h0 := GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants a d (fun τ => (-m τ).toNat) ν hP hInv hleft ρ hmeas hsurj Λ R hperp
  have hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun g τ => by
    rw [← norm_ne_zero_iff, norm_det_unitary]; exact one_ne_zero
  have hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) =
      ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ)) := by
    intro g
    refine Finset.prod_congr rfl fun τ _ => ?_
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.det_fin_zero]
    · have hm : m τ ≤ 0 := by
        by_contra h
        exact hpos ⟨ha, τ, by omega⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
      detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
    intro g
    unfold detChar
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]
  have hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R := by
    rw [hRdef]; abel
  have hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) =
      ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) +
        (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) R) := by
    intro g

    rw [hD g, hmono, map_add (f := _), map_sum, map_add (f := _), map_sum, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]
    rw [show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
        ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          Λ (prodMinors (U p))) =
        ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          (((r p : ℚ) : ℂ) * Λ (prodMinors (U p))) by ring, hinv g, one_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  rw [integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]
  simp

end GlobalTheory.MinorFrame.AvgCore
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinorsStatement

section

@[expose] public section

open Classical MeasureTheory

theorem _root_.GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  first | exact @GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors | exact GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors | (intros; apply GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors <;> assumption)
end
end
