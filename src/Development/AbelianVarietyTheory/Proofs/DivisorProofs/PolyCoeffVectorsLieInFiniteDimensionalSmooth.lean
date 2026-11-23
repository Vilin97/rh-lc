module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveraginStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimStablePolyAveragesWeights

section

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1
open ReciprocityTheory.ChartRestriction.DS (IsURepOn UJset)

namespace GlobalTheory.PsCo.PolyAvg

variable {n : ℕ}

theorem totalDegree_bind_le {α β : Type} (g : α → MvPolynomial β ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial α ℂ) : (bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical

  conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg i))).trans ?_
  simp [Finsupp.sum]

theorem exists_translate (a : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g, ev (a * g) P = ev g Q := by
  let f : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Poly n := Sum.elim
    (fun x => ∑ c, C (a x.1 c) * X (Sum.inl (c, x.2))) (fun x => ∑ c, C (star (a x.1 c)) * X (Sum.inr (c, x.2)))
  refine ⟨bind₁ f P, totalDegree_bind_le f ?_ P, fun g => ?_⟩
  · rintro (x | x) <;>
    · refine totalDegree_finsetSum_le fun l _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
  · have h : ev (a * g) = (ev g).comp (bind₁ f : Poly n →ₐ[ℂ] Poly n).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) ?_
      · simp [ev]
      · rintro (x | x) <;> simp [ev, f, Matrix.mul_apply, bind₁_X_right]
    rw [h]; rfl

def varWt : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Fin n → ℝ :=
  Sum.elim (fun x => -Pi.single x.1 1) (fun x => Pi.single x.1 1)

def monWt (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) : Fin n → ℝ := fun a => ∑ i, (s i : ℝ) * varWt i a

theorem ev_diag_monomial (θ : Fin n → ℝ) (g : Mat n) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    ev (Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) * g) (monomial s 1) =
      Complex.exp (((∑ a, monWt s a * θ a : ℝ) : ℂ) * Complex.I) * ev g (monomial s 1) := by
  have h1 : (∑ a, monWt s a * θ a : ℝ) = ∑ i, (s i : ℝ) * ∑ a, varWt i a * θ a := by
    simp only [monWt, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h1]
  simp only [ev, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul, ← mul_pow]
  congr 1
  rcases i with x | x
  · simp [varWt, Pi.single_apply, ite_mul]
  · simp [varWt, Pi.single_apply, ite_mul, ← Complex.exp_conj]

theorem continuous_toMK (ε : Fin n → Bool) : Continuous fun k : KG ε => toMK k :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun g : Mat n => ev g P := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi ?_)
  rintro (x | x)
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ UJset ε := (k : Formalism.REAL.UJ ε).2

theorem toMK_mul (ε : Fin n → Bool) (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Mat n → (H →L[ℂ] H)}

omit [CompleteSpace H] in
theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) :
    Integrable (fun k : KG ε => ev (toMK k) P • σ (toMK k) u) (muK ε) := by
  have h : Continuous fun k : KG ε => ev (toMK k) P • σ (toMK k) u :=
    ((continuous_ev P).comp (continuous_toMK ε)).smul
      ((hσ.2.2 u).comp_continuous (continuous_toMK ε) (toMK_mem ε))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def avg (hσ : IsURepOn (UJset ε) σ) (u : H) : Poly n →ₗ[ℂ] H where
  toFun P := ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)
  map_add' P Q := by
    rw [← integral_add (integrable_avg hσ u P) (integrable_avg hσ u Q)]
    simp only [map_add (f := _), add_smul]
  map_smul' c P := by
    rw [RingHom.id_apply, ← integral_smul]
    simp [ev, smul_eq_C_mul, mul_smul]

theorem apply_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) (g : KG ε) :
    σ (toMK g) (avg hσ u P) = ∫ k : KG ε, ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u ∂(muK ε) := by
  change σ (toMK g) (∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ u P),
    ← integral_mul_left_eq_self (fun k : KG ε => ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [← toMK_mul, inv_mul_cancel_left, toMK_mul, hσ.1.2 _ (toMK_mem ε g) _ (toMK_mem ε k), map_smul]
  rfl

theorem isWtOn_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (monWt s) (avg hσ u (monomial s 1)) := by
  intro θ hθ
  rw [← Formalism.REAL.range_toMK] at hθ
  obtain ⟨g, hg⟩ := hθ
  simp only at hg
  have hinv : toMK g⁻¹ = Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) := by
    have h1 : toMK g * Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) = 1 := by
      rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : toMK g⁻¹ * toMK g = 1 := by rw [← toMK_mul, inv_mul_cancel]; rfl
    rw [← Matrix.mul_one (toMK g⁻¹), ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← hg, apply_avg, hinv]
  simp only [ev_diag_monomial, mul_smul]
  rw [integral_smul]
  rfl

theorem polyAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  intro n ε d
  refine ⟨monWt '' {s | s.degree ≤ d}, (Finsupp.finite_of_degree_le d).image _, ?_⟩
  intro H _ _ _ σ hσ u
  refine ⟨(restrictTotalDegree _ ℂ d).map (avg hσ u), inferInstance, ?_, ?_, ?_⟩
  · rintro g hg v ⟨P, hP, rfl⟩
    rw [← Formalism.REAL.range_toMK] at hg
    obtain ⟨g, rfl⟩ := hg
    obtain ⟨Q, hQ, hQ'⟩ := exists_translate (toMK g⁻¹) P
    refine ⟨Q, (mem_restrictTotalDegree _ _ _).2 (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)), ?_⟩
    simp only
    rw [apply_avg]
    simp only [hQ']
    rfl
  · intro P hP
    exact ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, rfl⟩
  · rintro μ v ⟨P, hP, rfl⟩ hv hw
    by_contra hμ
    apply hv
    have hP' : P.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).1 hP
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have e : avg hσ u P = ∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1) := by

      conv_lhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    generalize avg hσ u P = v at e hw
    have : inner ℂ v (∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1)) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [inner_smul_right, ReciprocityTheory.ChartRestriction.DS.kfin_wt_orth hσ hw (isWtOn_avg hσ u s), mul_zero]
      rintro rfl
      exact hμ ⟨s, (le_totalDegree hs).trans hP', rfl⟩
    rwa [← e] at this

end GlobalTheory.PsCo.PolyAvg

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimStablePolyAveragesWeightsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_finiteDim_stable_polyAverages_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  first | exact @GlobalTheory.PsCo.PolyAvg.polyAvg | exact GlobalTheory.PsCo.PolyAvg.polyAvg | (intros; apply GlobalTheory.PsCo.PolyAvg.polyAvg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompact

section

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3.ReproPf

variable {n : ℕ} (ε : Fin n → Bool)

def pt (k : KG ε) : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
  Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2))

theorem continuous_toMK : Continuous fun k : KG ε => toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_pt : Continuous (pt ε) := by
  refine continuous_pi fun v => ?_
  rcases v with x | x
  · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε))
  · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε)))

def evL : Poly n →ₗ[ℂ] (KG ε → ℂ) where
  toFun P k := eval (pt ε k) P
  map_add' P Q := by ext k; simp
  map_smul' c P := by ext k; simp [MvPolynomial.smul_eval]

theorem continuous_evL (P : Poly n) : Continuous (evL ε P) :=
  (MvPolynomial.continuous_eval P).comp (continuous_pt ε)

def Fd (d : ℕ) : Submodule ℂ (KG ε → ℂ) := (restrictTotalDegree _ ℂ d).map (evL ε)

instance (d : ℕ) : FiniteDimensional ℂ (Fd ε d) := by
  unfold Fd; infer_instance

theorem continuous_of_mem {d : ℕ} {f : KG ε → ℂ} (hf : f ∈ Fd ε d) : Continuous f := by
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.1 hf
  exact continuous_evL ε P

theorem integrable_of_cont {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem star_evL (P : Poly n) : ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧
    ∀ k, star (evL ε P k) = evL ε Q k := by
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) P), ?_, fun k => ?_⟩
  · exact (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ _))
  · change (starRingEnd ℂ) (eval (pt ε k) P) = eval (pt ε k) (rename Sum.swap (map (starRingEnd ℂ) P))
    rw [eval_rename, eval_map, ← coe_eval₂Hom]
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp, eval_X, coe_eval₂Hom, eval₂_X]
      rcases v with x | x <;> simp [pt]

def gram (d : ℕ) : Fd ε d →ₗ[ℂ] Module.Dual ℂ (Fd ε d) :=
  LinearMap.mk₂ ℂ (fun g f => ∫ k, (g : KG ε → ℂ) k * (f : KG ε → ℂ) k ∂(muK ε))
    (fun g g' f => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g'.2).mul (continuous_of_mem ε f.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun g f f' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f'.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact integral_const_mul c _)

theorem gram_injective (d : ℕ) : Function.Injective (gram ε d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  obtain ⟨P, hP, hgP⟩ := Submodule.mem_map.1 g.2
  obtain ⟨Q, hQ, hQk⟩ := star_evL ε P
  have hQm : evL ε Q ∈ Fd ε d :=
    Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2
      (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)))
  have h0 := LinearMap.congr_fun hg ⟨evL ε Q, hQm⟩
  simp only [gram, LinearMap.mk₂_apply, LinearMap.zero_apply] at h0
  have hc : Continuous (g : KG ε → ℂ) := continuous_of_mem ε g.2
  have e1 : ∀ k, (g : KG ε → ℂ) k * evL ε Q k = ((‖(g : KG ε → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← hQk, ← hgP, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  simp_rw [e1, integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  have hnn : 0 ≤ᵐ[muK ε] fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := Filter.Eventually.of_forall fun k => by positivity
  have hc2 : Continuous fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := hc.norm.pow 2
  have hint : Integrable (fun k => ‖(g : KG ε → ℂ) k‖ ^ 2) (muK ε) :=
    integrableOn_univ.1 (hc2.continuousOn.integrableOn_compact isCompact_univ)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hfun := (hc2.ae_eq_iff_eq (muK ε) continuous_const).1 hae
  ext k
  have h1 : ‖(g : KG ε → ℂ) k‖ ^ 2 = 0 := congrFun hfun k
  have h2 : (g : KG ε → ℂ) k = 0 := by simpa using h1
  simpa using h2

theorem fock_reproducing_formula : Repro := by
  intro n ε d
  have hfin : Module.finrank ℂ (Fd ε d) = Module.finrank ℂ (Module.Dual ℂ (Fd ε d)) :=
    (Subspace.dual_finrank_eq).symm
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 (gram_injective ε d)
  let Λ : Module.Dual ℂ (Fd ε d) := (LinearMap.proj (R := ℂ) (φ := fun _ : KG ε => ℂ) 1).comp (Fd ε d).subtype
  obtain ⟨g, hg⟩ := hs Λ
  obtain ⟨Q, hQ, hgQ⟩ := Submodule.mem_map.1 g.2
  refine ⟨Q, (mem_restrictTotalDegree _ _ _).1 hQ, fun P hP => ?_⟩
  have h := LinearMap.congr_fun hg ⟨evL ε P, Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2 hP)⟩
  simp only [gram, LinearMap.mk₂_apply, Λ, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.proj_apply] at h
  rw [← hgQ] at h
  exact h.symm

end GlobalTheory.PsCo.Pc3.ReproPf

namespace GlobalTheory.PsCo.Pc3

theorem fock_reproducing_formula : Repro := ReproPf.fock_reproducing_formula

end GlobalTheory.PsCo.Pc3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompactStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact : GlobalTheory.PsCo.Pc3.Repro := by
  first | exact @GlobalTheory.PsCo.Pc3.fock_reproducing_formula | exact GlobalTheory.PsCo.Pc3.fock_reproducing_formula | (intros; apply GlobalTheory.PsCo.Pc3.fock_reproducing_formula <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth

section

@[expose] public section

namespace GlobalTheory.PsCo.Pc3

theorem uFin : UFin := GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact GlobalTheory.T.exists_finiteDim_stable_polyAverages_weights

end GlobalTheory.PsCo.Pc3
end
end
