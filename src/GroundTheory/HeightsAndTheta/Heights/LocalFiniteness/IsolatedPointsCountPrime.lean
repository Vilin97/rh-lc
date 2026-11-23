module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpenPoly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Algebra.MvPolynomial
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem IsolatedPointsCountPrime.exists_dim_eq {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_quotient_le J
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k => exact ⟨k, rfl⟩

theorem IsolatedPointsCountPrime.eval_aeval {n m : ℕ} (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin m) ℂ) (x : Fin n → ℂ) :
    eval x (aeval Q f) = eval (fun i => eval x (Q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' => rw [map_add (f := _), map_add (f := _), hp, hp', map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem IsolatedPointsCountPrime.exists_eval_ne_zero {d : ℕ} {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0)
    {w : Fin d → ℂ} {S : Set (Fin d → ℂ)} (hS : S ∈ 𝓝 w) : ∃ w' ∈ S, eval w' Δ ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hΔ
  refine funext_set (fun i => Metric.ball (w i) ε)
    (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hball ?_)
  rw [ball_pi w hε]
  exact hy

theorem IsolatedPointsCountPrime.proof (hOpen : IsolatedFibreOpenPoly.Statement)
    (hDom : DominantFibreBound.Statement) (hDim : ImageDimLe.Statement) :
    IsolatedPointsCountPrime.Statement := by
  classical
  intro n m P hP Q

  have hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime := RingHom.ker_isPrime _
  set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK
  obtain ⟨d, hd⟩ := IsolatedPointsCountPrime.exists_dim_eq P
  obtain ⟨r, hr⟩ := IsolatedPointsCountPrime.exists_dim_eq K
  have hrd : r ≤ d := by
    have h := hDim n m P Q hP
    rw [← hK, hr, hd] at h
    exact_mod_cast h
  obtain ⟨B, hB⟩ := (GenericProjectionFinite.full m r K hKp hr).2.1
  have hfib := FibreBound.full m r K B hKp hr hB

  set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm
  have hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K := by
    intro x hx f hf
    have hf' : aeval Q f ∈ P := by
      rw [hK, RingHom.mem_ker] at hf
      change Ideal.Quotient.mk P (aeval Q f) = 0 at hf
      exact Ideal.Quotient.eq_zero_iff_mem.mp hf
    rw [← IsolatedPointsCountPrime.eval_aeval]
    exact hx _ hf'
  have hQc : Continuous Qm := continuous_pi fun i => MvPolynomial.continuous_eval _

  set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq
  have hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x) := by
    intro x
    funext i

    simp only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X,
    Matrix.mulVec, dotProduct, hQm]

  have step1 : ∀ z x, x ∈ isolatedFibrePts P Q z →
      ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x := by
    rintro z x ⟨hxP, hxQ, V, hV, hiso⟩
    have hQx : Qm x = z := funext hxQ
    have hfin : (fibre K B (B.mulVec z) \ {z}).Finite := (hfib (B.mulVec z)).2.1.subset Set.sdiff_subset
    have hO : (fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x) := by
      rw [hQx]
      exact hfin.isClosed.compl_mem_nhds fun h => h.2 rfl
    refine ⟨V ∩ Qm ⁻¹' (fibre K B (B.mulVec z) \ {z})ᶜ,
      Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩
    rintro x' ⟨hx'P, hx'V, hx'O⟩ hx'q
    refine hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i
    have h1 : B.mulVec (Qm x') = B.mulVec z := by
      rw [← hqe, ← hQx, ← hqe]
      funext i
      exact hx'q i
    by_contra hne
    exact hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩
  rcases lt_or_eq_of_le hrd with hlt | rfl
  ·
    refine ⟨0, fun z => ?_⟩
    suffices isolatedFibrePts P Q z = ∅ by simp [this]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨W, hW, hiso⟩ := step1 z x hx
    set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp
    have hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x :=
      ⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by
        simpa [hp, i.isLt] using h ⟨i, i.isLt.trans hlt⟩⟩
    have himg := hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem
    set px : Fin d → ℂ := fun i => eval x (p i) with hpx
    set j : Fin d := ⟨r, hlt⟩
    have hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆
        {w | w j = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp [hp, j]
    have hc : Continuous fun t : ℂ => Function.update px j t := continuous_const.update j continuous_id
    have h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [Function.update_eq_self]
      exact Filter.mem_of_superset himg hsub
    have h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0} := by
      intro t ht
      simpa using ht
    exact (infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)
  ·
    have hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q)) := by
      have hcomp : aeval q = (aeval Q).comp (pullback B) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [hq, pullback]
      intro a b hab
      apply hB.injective
      simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢
      rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub] at hab
      rw [hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hab
    obtain ⟨e, Δ, hΔ, hbound⟩ := hDom n r P q hP hd hinj
    refine ⟨e, fun z => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have htc' : t.encard = ((e + 1 : ℕ) : ℕ∞) := by rw [htc]; push_cast; rfl
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc'
    obtain ⟨U, hUo, hUd⟩ := htf.t2_separation
    have hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈
        𝓝 (B.mulVec z) := by
      intro x hx
      have hx' := hts hx
      obtain ⟨W, hW, hiso⟩ := step1 z x hx'
      have h := hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)
      have e1 : (fun i => eval x (q i)) = B.mulVec z := by
        rw [hqe]
        congr 1
        exact funext hx'.2.1
      rwa [e1] at h
    have hI := (Filter.biInter_mem htf).2 hw
    obtain ⟨w', hw'I, hΔw'⟩ := IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI
    have hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w' :=
      fun x hx => Set.mem_iInter₂.1 hw'I x hx
    choose! g hg1 hg2 using hpick
    have hinjg : Set.InjOn g t := by
      intro x hx y hy hxy
      by_contra hne
      refine Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_
      rw [hxy]
      exact (hg1 y hy).2
    have himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩
    have hle := (Set.encard_le_encard himg).trans (hbound w' hΔw')
    rw [hinjg.encard_image, htc'] at hle
    have hle' : e + 1 ≤ e := by exact_mod_cast hle
    omega

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem eventually_const_mem_ball_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

theorem analyticAt_comp_const_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by
  have hc : Differentiable ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) :=
    differentiable_pi.2 fun _ ↦ differentiable_id
  exact DifferentiableOn.analyticAt (s := (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) ⁻¹' Metric.ball 0 r)
    (hφ.comp hc.differentiableOn fun _ h ↦ h) (eventually_const_mem_ball_one hr)

theorem analyticAt_eval_of_analyticAt_zero {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)

theorem branchOrder_ne_top_of_not_mem (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by
  intro htop
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
  have hU : Metric.ball (0 : Fin 1 → ℂ) (min ε γ.radius) ⊆ Metric.ball 0 γ.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨t, ht, hne⟩ := hB n 1 J b _ γ.toFun hJ hdim hb Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (lt_min hε γ.radius_pos)⟩ (γ.differentiableOn.mono hU) (γ.injOn.mono hU)
    fun t ht ↦ γ.mapsTo (hU ht)
  have ht0 : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
  apply hne
  rw [← ht0]
  apply hεb
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (norm_le_pi_norm t 0) (lt_of_lt_of_le ht (min_le_left _ _))

theorem SameOrdersLiftCentre.proof (hB : BranchOffHypersurface.Statement) : SameOrdersLiftCentre.Statement := by
  intro n J q M γ γ' Γ Γ' hJ hdim hΓd hΓ hΓ'd hΓ' hord
  funext s
  rcases s with j | i
  · have e := congrFun (hΓ 0 (Metric.mem_ball_self γ.radius_pos)).2 j
    have e' := congrFun (hΓ' 0 (Metric.mem_ball_self γ'.radius_pos)).2 j
    simp only [firstCoords] at e e'
    rw [e, e', γ.map_zero, γ'.map_zero]
  obtain ⟨a, b, hb, hab⟩ := M.birational i

  have key : ∀ (c : VarBranch J 1 q) (L : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
      DifferentiableOn ℂ L (Metric.ball 0 c.radius) →
      (∀ τ ∈ Metric.ball 0 c.radius, L τ ∈ zeroSetIn M.ideal ∧ firstCoords (L τ) = c.toFun τ) → ∀ l : ℂ,
      branchOrder c (a - C l * b) =
        branchOrder c b + analyticOrderAt (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 := by
    intro c L hLd hL l
    have hLa : AnalyticAt ℂ (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
      ((analyticAt_pi_iff.mp (analyticAt_comp_const_one c.radius_pos hLd)) (Sum.inr i)).sub analyticAt_const
    have hBa := analyticAt_eval_of_analyticAt_zero (analyticAt_comp_const_one c.radius_pos c.differentiableOn) b
    rw [branchOrder, branchOrder, ← analyticOrderAt_mul hBa hLa]
    apply analyticOrderAt_congr
    filter_upwards [eventually_const_mem_ball_one c.radius_pos] with τ hτ
    have h := (hL _ hτ).1 _ hab
    simp only [eval_sub, eval_mul, eval_X, eval_rename] at h
    change eval (firstCoords (L fun _ ↦ τ)) b * _ - eval (firstCoords (L fun _ ↦ τ)) a = 0 at h
    rw [(hL _ hτ).2] at h
    simp only [eval_sub, eval_mul, eval_C, Pi.mul_apply]
    linear_combination -h
  set l := Γ 0 (Sum.inr i)
  have k1 := key γ Γ hΓd hΓ l
  have k2 := key γ' Γ' hΓ'd hΓ' l
  rw [← hord, ← hord] at k2
  have heq := WithTop.add_left_cancel (branchOrder_ne_top_of_not_mem hB γ hJ hdim hb) (k1.symm.trans k2)
  have hGa : AnalyticAt ℂ (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ.radius_pos hΓd)) (Sum.inr i)).sub analyticAt_const
  have hG'a : AnalyticAt ℂ (fun τ : ℂ ↦ Γ' (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ'.radius_pos hΓ'd)) (Sum.inr i)).sub analyticAt_const
  have hz : analyticOrderAt (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 ≠ 0 :=
    hGa.analyticOrderAt_ne_zero.2 (sub_self _)
  rw [heq] at hz
  exact (sub_eq_zero.1 (hG'a.analyticOrderAt_ne_zero.1 hz)).symm

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCountPrime

section

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime : GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.proof GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly.full GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound GroundTheory.Heights₂.Heights.ImageDimLe.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre : GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.Statement :=
  @GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.proof GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds
end
end
