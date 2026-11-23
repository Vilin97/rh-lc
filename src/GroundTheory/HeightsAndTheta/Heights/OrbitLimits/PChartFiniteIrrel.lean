module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartFiniteIrrel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrelPow

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]
  [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ChartFiniteIrrel.weighted_le_pow (t : ℕ) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      ((Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))) ^
        t).restrictScalars F := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single,
      Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    have hm' : ∀ k, ∑ i, m ⟨k, i⟩ = t + 1 := fun k => congrFun ((weight_mw m).symm.trans hm) k
    have hj : ∀ k, ∃ i, m ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => m ⟨k, i⟩) (by rw [hm' k]; omega)
      exact ⟨i, hi⟩
    choose j hj using hj
    let d : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = j p.1 then 1 else 0
    have hd : ∀ k i, d ⟨k, i⟩ = if i = j k then 1 else 0 := fun k i => rfl
    have hdm : d ≤ m := Finsupp.le_def.mpr fun ⟨k, i⟩ => by
      rw [hd]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hj k)
      · exact Nat.zero_le _
    have h1 : ∀ k, ∑ i, d ⟨k, i⟩ = 1 := fun k => by simp [hd]
    have hsum : ∀ k, ∑ i, (m - d) ⟨k, i⟩ = t := fun k => by
      have h2 : ∑ i, ((m - d) ⟨k, i⟩ + d ⟨k, i⟩) = t + 1 := by
        rw [← hm' k]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finsupp.tsub_apply]; exact Nat.sub_add_cancel (Finsupp.le_def.mp hdm _)
      rw [Finset.sum_add_distrib, h1] at h2; omega
    have hmd := monomial_mem_weighted (F := F) (m - d) 1
    rw [show (fun k => ∑ i, (m - d) ⟨k, i⟩) = fun _ => t from funext hsum] at hmd
    have hd1 := monomial_mem_weighted (F := F) d 1
    rw [show (fun k => ∑ i, d ⟨k, i⟩) = fun _ => 1 from funext h1] at hd1
    show AddMonoidAlgebra.single m (1 : F) ∈ _
    rw [single_eq_monomial, ← tsub_add_cancel_of_le hdm, ← one_mul (1 : F), ← monomial_mul, pow_succ]
    exact Ideal.mul_mem_mul (ih hmd) (Ideal.subset_span hd1)

end

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

section Devissage

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem sup_span_inf_eq' {I : Ideal (MRingOver F ι)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) {g : MRingOver F ι}
    {δ : K → ℕ} (hg : g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ) {d : K → ℕ} (hd : δ ≤ d) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ (I ⊔ Ideal.span {g}).restrictScalars F =
      (weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ I.restrictScalars F) ⊔
        (weightedHomogeneousSubmodule F (mw (ι := ι)) (d - δ)).map (LinearMap.mulLeft F g) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨hxd, hx⟩ := Submodule.mem_inf.mp hx
    rw [Submodule.restrictScalars_mem, Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hdd : d - δ + δ = d := tsub_add_cancel_of_le hd
    have key := DirectSum.coe_decompose_mul_add_of_right_mem
      (𝒜 := weightedHomogeneousSubmodule F (mw (ι := ι))) (a := c) (i := d - δ) hg
    rw [hdd] at key
    have hx' := DirectSum.decompose_of_mem_same (ℳ := weightedHomogeneousSubmodule F (mw (ι := ι))) hxd
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, key] at hx'
    rw [← hx']
    refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨SetLike.coe_mem _, ?_⟩)
      (Submodule.mem_map.mpr ⟨_, SetLike.coe_mem
        ((DirectSum.decompose (weightedHomogeneousSubmodule F (mw (ι := ι))) c) (d - δ)), ?_⟩)
    · rw [Submodule.restrictScalars_mem]
      exact hI d ha
    · rw [LinearMap.mulLeft_apply, mul_comm]
  · refine sup_le (inf_le_inf_left _ ?_) ?_
    · intro x hx
      rw [Submodule.restrictScalars_mem] at hx ⊢
      exact Ideal.mem_sup_left hx
    · rintro y ⟨z, hz, rfl⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [LinearMap.mulLeft_apply]
        have := SetLike.GradedMul.mul_mem hg hz
        rwa [add_tsub_cancel_of_le hd] at this
      · rw [Submodule.restrictScalars_mem, LinearMap.mulLeft_apply]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))

end Devissage

section Lex

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem weighted_le_of_irrel {P : Ideal (MRingOver F ι)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MRingOver F ι) ∈ P) {e : K → ℕ} (he : 1 ≤ e k) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) e ≤ P.restrictScalars F := by
  intro x hx
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [Submodule.restrictScalars_mem, x.as_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hw := hx (mem_support_iff.mp hm)
  obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : Finsupp.weight (mw (ι := ι)) m k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      rcases p with ⟨k', j⟩
      simp only [mw, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k' = k
      · subst hk
        simp [hcon j]
      · simp [Pi.single_apply, Ne.symm hk]
    rw [hw] at h0
    omega
  have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    omega
  have hmono : monomial m (AddMonoidAlgebra.coeff x m) =
      monomial (m - Finsupp.single ⟨k, i⟩ 1) (AddMonoidAlgebra.coeff x m) * X ⟨k, i⟩ := by
    rw [X, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  rw [hmono]
  exact Ideal.mul_mem_left _ _ (hk i)

end Lex

section Len

variable {R : Type*} [CommRing R]

end Len

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrel

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartFiniteIrrel.proof : ChartFiniteIrrel.Statement.{u, v, w} := by
  intro K _ ι _ F _ V f i hV hf hirr
  classical
  let _ := MvPolynomial.weightedGradedAlgebra F (mw (ι := ι))
  let M : Ideal (MRingOver F ι) :=
    Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))
  have hMrad : M ≤ (V ⊔ Ideal.span {f}).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun W hW => Ideal.span_le.mpr fun x hx => ?_
    have h := hirr W hW
    simp only [IsRelevant, not_forall, not_exists, not_not] at h
    obtain ⟨k, hk⟩ := h
    exact weighted_le_of_irrel (e := fun _ => 1) hk le_rfl hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hMrad (IsNoetherian.noetherian M)
  have hA : ∀ t, N ≤ t → weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      (V ⊔ Ideal.span {f}).restrictScalars F := fun t ht _ hh =>
    hN (Ideal.pow_le_pow_right ht (ChartFiniteIrrel.weighted_le_pow t hh))
  have hVh : V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
    obtain ⟨S₀, hS₀, rfl⟩ := hV
    exact Ideal.homogeneous_span _ S₀ fun x hx =>
      let ⟨a, ha⟩ := hS₀ x hx; ⟨a, mem_weighted_of_isMultiHomog ha⟩
  let π := (Ideal.Quotient.mkₐ F (chartIdeal V i)).toLinearMap
  let B : ℕ → Submodule F (MRingOver F ι ⧸ chartIdeal V i) := fun t =>
    (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t)).map π
  have hmono : ∀ t, B t ≤ B (t + 1) := by
    rintro t _ ⟨h, hh, rfl⟩
    refine ⟨h * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (fun _ : K => 1) k,
      SetLike.mul_mem_graded hh (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i _)), ?_⟩
    simp [π, map_prod, mk_chartIdeal_X_self]
  have hstep : ∀ t, N ≤ t + 1 → B (t + 1) ≤ (B t).map (LinearMap.mulLeft F (π f)) := by
    rintro t ht _ ⟨h, hh, rfl⟩
    have h2 : h ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t + 1) ⊓
        (V ⊔ Ideal.span {f}).restrictScalars F := ⟨hh, hA _ ht hh⟩
    rw [sup_span_inf_eq' hVh (mem_weighted_of_isMultiHomog hf) (d := fun _ => t + 1) (fun _ => Nat.le_add_left 1 t),
      show ((fun _ : K => t + 1) - fun _ => 1) = fun _ => t from funext fun _ => by simp] at h2
    obtain ⟨v, ⟨-, hv⟩, _, ⟨g, hg, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h2
    refine ⟨π g, ⟨g, hg, rfl⟩, ?_⟩
    have hv0 : Ideal.Quotient.mk (chartIdeal V i) v = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hv)
    simp [π, hv0]
  have heq : ∀ t, N ≤ t → B t = B (t + 1) := fun t ht =>
    Submodule.eq_of_le_of_finrank_le (hmono t)
      ((Submodule.finrank_mono (hstep t (by omega))).trans (Submodule.finrank_map_le _ _))
  have hconst : ∀ t, N ≤ t → B t = B N := fun t ht => by
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [← heq t ht, ih]
  have htop : B N = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨e₀, he₀⟩ := exists_homog_chart V i b
    obtain ⟨b', hb', hbb⟩ := he₀ (fun _ => N + ∑ k, e₀ k) fun k =>
      le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    rw [← hconst _ (Nat.le_add_right _ _)]
    exact ⟨b', hb', hbb⟩
  rw [Module.finite_def, ← htop]
  exact Module.Finite.iff_fg.mp inferInstance

end GroundTheory.Heights₂.Heights.Targets
end
end
