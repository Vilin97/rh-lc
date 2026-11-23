module

public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.HeisenbergActionAddOfOrthogonal
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchSlice
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ContinuousOnRationalWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

-- Source module: Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.RationalWeightSuccMulInvNorm

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate

variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]

abbrev XS (j : Type) : Type := PiLp 2 fun _ : j => ℂ

def pim (ξ : K → ι → n → ℂ) (p : K × (ι → ℂ)) : XS (ι × n) := WithLp.toLp 2 fun j => 2 * (p.2 j.1 * ξ p.1 j.1 j.2)

def bet (ξ : K → ι → n → ℂ) (q : K × XS (ι × n)) : ι → ℂ := fun w => ∑ i, ξ q.1 w i * conj (q.2 (w, i))

omit [TopologicalSpace K] in
theorem pr_bet (ξ : K → ι → n → ℂ) (k : K) (η : XS (ι × n)) (t : ι → ℂ) : pr (bet ξ (k, η)) t = ⟪η, pim ξ (k, t)⟫ := by
  simp only [pr, bet, pim, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul, Complex.re_sum, Finset.mul_sum, Complex.inner]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  simp; ring

theorem cont_bet {ξ : K → ι → n → ℂ} (h : Continuous ξ) : Continuous (bet ξ) := by unfold bet; fun_prop

theorem bet_le [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) : ∃ D : ℝ, ∀ k η, ‖bet ξ (k, η)‖ ≤ D * ‖η‖ := by
  obtain ⟨C, hC⟩ := (isCompact_range h).isBounded.exists_norm_le
  refine ⟨Fintype.card n * |C|, fun k η => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖ξ k w i‖ ≤ |C| := ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ w)).trans ((hC _ ⟨k, rfl⟩).trans (le_abs_self C))
  exact mul_le_mul h1 (PiLp.norm_apply_le η (w, i)) (norm_nonneg _) (abs_nonneg _)

theorem exists_lb {α : Type} [TopologicalSpace α] [CompactSpace α] {g : α → ι → ℝ} (h : ∀ w, Continuous fun a => g a w)
    (hp : ∀ a w, 0 < g a w) : ∃ m : ℝ, 0 < m ∧ ∀ a w, m ≤ g a w := by
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous fun q : α × ι => g q.1 q.2 := continuous_prod_of_discrete_right.2 h
  obtain ⟨m, hm, hb⟩ := isCompact_univ.exists_forall_le' hc.continuousOn (a := 0) fun q _ => hp q.1 q.2
  exact ⟨m, hm, fun a w => hb (a, w) trivial⟩

theorem prp_pim [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) (hne : ∀ k w, ξ k w ≠ 0) (k₁ : K) :
    Prp (pim ξ) (pim ξ (k₁, 1)) := by
  refine ⟨by unfold pim; fun_prop, ⟨_, rfl⟩, ?_⟩
  obtain ⟨m, hm, hb⟩ := exists_lb (g := fun k w => ‖ξ k w‖) (fun w => by fun_prop) fun k w => norm_pos_iff.2 (hne k w)
  refine ⟨m, {p | ∀ w, m / 2 ≤ ‖p.2 w‖ * ‖ξ p.1 w‖} ∩ univ ×ˢ Metric.closedBall 0 ((‖ξ k₁‖ + m) / m), hm, ?_, ?_, fun p hp => ?_⟩
  · refine IsCompact.inter_left (isCompact_univ.prod (isCompact_closedBall _ _)) ?_
    simp only [setOf_forall]
    exact isClosed_iInter fun w => isClosed_le continuous_const (by fun_prop)
  · intro p hp w h0
    have := hp.1 w
    rw [h0, norm_zero, zero_mul] at this
    linarith
  · have key : ∀ w, ‖p.2 w • ξ p.1 w - ξ k₁ w‖ ≤ m / 2 := fun w => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      have h1 := (PiLp.norm_apply_le (pim ξ p - pim ξ (k₁, 1)) (w, i)).trans ((dist_eq_norm _ _).symm.le.trans hp)
      have h2 : (pim ξ p - pim ξ (k₁, 1)) (w, i) = 2 * (p.2 w • ξ p.1 w - ξ k₁ w) i := by simp [pim]; ring
      rw [h2, norm_mul, Complex.norm_ofNat] at h1
      linarith
    refine ⟨fun w => ?_, trivial, ?_⟩
    · have := norm_sub_norm_le (ξ k₁ w) (p.2 w • ξ p.1 w)
      rw [norm_sub_rev, norm_smul] at this
      linarith [key w, hb k₁ w]
    · rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      have := norm_sub_norm_le (p.2 w • ξ p.1 w) (ξ k₁ w)
      rw [norm_smul] at this
      rw [le_div_iff₀ hm]
      nlinarith [key w, hb p.1 w, norm_le_pi_norm (ξ k₁) w, norm_nonneg (p.2 w)]

theorem exists_FT_ne {a : (ι → ℂ) → ℂ} (ha : Continuous a) (hi : Integrable a) (h0 : a 0 ≠ 0) : ∃ t, FT a t ≠ 0 := by
  by_contra hn
  push Not at hn
  let π : (ι → ℂ) → XS ι := fun x => WithLp.toLp 2 fun w => 2 * x w
  have hπ : Continuous π := by fun_prop
  obtain ⟨φ, -, -, hφ⟩ := core_bump volume π hπ 0 (fun x => a x * (a 0)⁻¹) univ (Metric.closedBall 0 1) isOpen_univ
    (ha.mul continuous_const).continuousOn (isCompact_closedBall _ _) (subset_univ _) 1 one_pos (fun x hx => by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
      have h1 := (PiLp.norm_apply_le (π x) w).trans ((dist_zero_right _).symm.le.trans hx)
      simp only [π, norm_mul, Complex.norm_ofNat] at h1
      linarith [norm_nonneg (x w)]) (fun x hx => by
      have : x = 0 := funext fun w => by simpa [π] using congrArg (fun y : XS ι => y w) hx
      simp [this, h0]) 0 (by ext w; simp [π])
  refine hφ (fourier_vanish _ π hπ.measurable _ (hi.mul_const _) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const]
  have := hn fun w => -conj (η w)
  rw [FT] at this
  refine mul_eq_zero_of_left (Eq.trans ?_ this) _
  congr 1; funext x; congr 2
  simp only [pr, π, PiLp.inner_apply, Complex.inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp; ring

theorem rationalWeight_succ_mul_inv_norm (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) :
    r0 κ (e + 1) x * ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ)⁻¹ = r0 κ e x := by
  have : ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
  rw [mul_inv_eq_iff_eq_mul₀ this]
  push_cast
  rw [r0, r0, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

theorem rationalWeight_eq_mul_norm_pow (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : r0 κ e x = r0 κ 0 x * ((nm x : ℝ) : ℂ) ^ e := by
  simp only [r0, nm]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

omit [TopologicalSpace K] in
theorem Dec.integrable {a : K × (ι → ℂ) → ℂ} (hd : Dec a) (k : K) (ha : Continuous fun x => a (k, x)) : Integrable fun x => a (k, x) := by
  obtain ⟨C, N, -, hC⟩ := hd.bound 0
  exact (integrable_mj.const_mul C).mono' ha.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC k x 0)

end PositivityTheory.ThKG.Loc.Bump

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.FormYx

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF
open scoped ComplexConjugate

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {lift : (InfinitePlace F → ℂ) → AE F E}

theorem IsLift.ext (h : IsLift σ B lift) {a b : AE F E} (hab : At (evI F) (a - b)) (e : ∀ w, piInf (B.emb w) a = piInf (B.emb w) b) :
    a = b := by
  have h0 : lift (fun w => piInf (B.emb w) 0) = 0 := h.inv 0 fun u _ => smul_zero u
  rw [← sub_eq_zero, ← h.inv _ hab, ← h0]
  congr 1; funext w; rw [map_sub, e, sub_self, map_zero]

theorem at_sub {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a - b) :=
  fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

theorem at_add {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a + b) :=
  fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_mul {a : AE F E} (ha : At (evI F) a) (b : AE F E) : At (evI F) (a * b) := at_smul2 ha b

theorem IsLift.eq (h : IsLift σ B lift) {a : AE F E} (ha : At (evI F) a) {c} (e : ∀ w, piInf (B.emb w) a = c w) : a = lift c :=
  h.ext (at_sub ha (h.supp c)) fun w => by rw [e, h.pi]

theorem IsLift.ch (h : IsLift σ B lift) {a b : AE F E} (ha : At (evI F) a) {x y : InfinitePlace F → ℂ} (hx : ∀ w, (piInf (B.emb w) (a * b)).re = (x w * y w).re) :
    B.ψ (Algebra.trace (AF F) (AE F E) (a * b)) = ch (-pr x y) := by
  rw [h.psi _ (at_mul ha b), Bump.ch, pr]
  simp only [hx]
  congr 1; push_cast; ring

theorem pi_bA (h : IsLift σ B lift) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → AE F E) (w) : piInf (B.emb w) (bA σ J x y) =
    (fun i => piInf (B.emb w) (x i)) ⬝ᵥ J.map (B.emb w).1 *ᵥ fun i => conj (piInf (B.emb w) (y i)) := by

  simp only [bA, dotProduct, Matrix.mulVec, map_sum, map_mul, h.conj, incM, Matrix.map_apply, h.incl]


variable (B) in
def xi (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) : InfinitePlace F → Fin n → ℂ :=
  fun w i => piInf (B.emb w) ((mat k.1⁻¹ *ᵥ incV F x) i)

theorem cont_xi (h : IsLift σ B lift) (x : Fin n → E) (S : Subgroup (UA σ X.J)) : Continuous (xi B x (S := S)) := by
  refine continuous_pi fun w => continuous_pi fun i => ?_

  simp only [xi, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine continuous_finsetSum _ fun j _ => ((h.cont w).comp ?_).mul continuous_const
  have : Continuous fun k : S => (((k.1.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (continuous_apply j).comp ((continuous_apply i).comp this)

theorem xi_ne (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)} (k : S) (w) : xi B x k w ≠ 0 := by
  intro h0
  have := pi_bA h X.J (mat k.1⁻¹ *ᵥ incV F x) (mat k.1⁻¹ *ᵥ incV F y) w
  rw [bA_mat, bA_inc, hxy, map_one, map_one] at this
  change _ = xi B x k w ⬝ᵥ _ at this
  rw [h0, zero_dotProduct] at this
  exact one_ne_zero this


variable (B X) in
def Yv (lift : (InfinitePlace F → ℂ) → AE F E) (η : XS (InfinitePlace F × Fin n)) : Fin n → AE F E :=
  fun i => lift fun w => conj (((X.J.map (B.emb w).1)⁻¹ *ᵥ fun j => conj (η (w, j))) i)

theorem at_Yv (h : IsLift σ B lift) (η) : At (evI F) (Yv X B lift η) := fun u hu => funext fun _ => h.supp _ u hu

theorem pi_beta (h : IsLift σ B lift) {r s} (hX : X.IsHerm σ B r s) (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) (η) (w) :
    piInf (B.emb w) (bA σ X.J (incV F x) (mat k.1 *ᵥ Yv X B lift η)) = bet (xi B x) (k, η) w := by
  rw [← mat_cancel' k.1 (incV F x), bA_mat, pi_bA h]
  simp only [Yv, h.pi, Complex.conj_conj]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (cartan_det (hX.cartan w)).isUnit, Matrix.one_mulVec]
  rfl

theorem sig_pt (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)}
    (hS : ∀ k ∈ S, k ∈ UAt σ X (evI F)) (p : S × (InfinitePlace F → ℂ)) (hp : pim (xi B x) p = pim (xi B x) ((1 : S), 1)) :
    (∀ w, p.2 w ≠ 0) ∧ ∃ t : (AE F E)ˣ, At (evI F) ((t : AE F E) - 1) ∧ (∀ w, piInf (B.emb w) (t : AE F E) = p.2 w) ∧
      mat p.1.1 *ᵥ incV F x = t.1 • incV F x := by
  have e : ∀ w i, p.2 w * xi B x p.1 w i = xi B x (1 : S) w i := fun w i => by
    simpa [pim] using congrArg (fun z : XS _ => z (w, i)) hp
  have hne : ∀ w, p.2 w ≠ 0 := fun w h0 => xi_ne h hxy (1 : S) w (funext fun i => by rw [← e, h0, zero_mul]; rfl)
  obtain ⟨t, ht, ht'⟩ := h.unit p.2 hne
  refine ⟨hne, t, ht, ht', ?_⟩
  have k1 : t.1 • (mat p.1.1⁻¹ *ᵥ incV F x) = incV F x := funext fun i => by
    refine h.ext ?_ fun w => ?_
    · have a1 : At (evI F) ((mat p.1.1⁻¹ - 1) *ᵥ incV F x) := fun u hu => by
        rw [← Matrix.smul_mulVec, hS _ (inv_mem p.1.2) u hu, Matrix.zero_mulVec]
      have a2 := at_add (at_smul2 ht (mat p.1.1⁻¹ *ᵥ incV F x)) a1
      rw [sub_smul, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_sub_cancel] at a2
      exact fun u hu => congrFun (a2 u hu) i
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, ht']
      refine (e w i).trans ?_
      simp [xi, mat_one]
  conv_lhs => rw [← k1, Matrix.mulVec_smul, mat_cancel']

theorem nu_eq (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w) {t : (AE F E)ˣ}
    (ht : At (evI F) ((t : AE F E) - 1)) : (ν t : ℂ) = r0 κ 0 (fun w => piInf (B.emb w) t) ∧
      (absE F E t : ℝ) = nm fun w => piInf (B.emb w) t := ⟨by rw [hν t ht]; simp [r0], h.abs t ht⟩

theorem conv (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    (x : @Measure (idAt E (evI F)) (borel _)) (hx : @Measure.IsHaarMeasure _ _ _ (borel _) x) : ∃ c : ℂ, c ≠ 0 ∧
    ∀ (e : ℕ) (g : (InfinitePlace F → ℂ) → ℂ) (G : (AE F E)ˣ → ℂ), (∀ t : (AE F E)ˣ, G t = g fun w => piInf (B.emb w) t) →
      @integral _ _ _ _ (borel _) x (fun t => G t.1 * (ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ (e + 1)) = c * ∫ y, g y * r0 κ e y := by
  obtain ⟨c, hc, H⟩ := h.haar x hx
  refine ⟨c, by exact_mod_cast hc.ne', fun e g G hG => ?_⟩
  have := H fun y => g y * r0 κ (e + 1) y
  rw [← show _ = ∫ y, g y * r0 κ e y from integral_congr_ae (by
    filter_upwards [ae_unit] with y hy
    exact (mul_assoc _ _ _).trans (congrArg _ (rationalWeight_succ_mul_inv_norm κ e hy))), ← this]
  congr 1; funext t
  obtain ⟨e1, e2⟩ := nu_eq h hν ((h.idAt t.1).1 t.2)
  rw [hG, rationalWeight_eq_mul_norm_pow κ (e + 1), e1, e2, mul_assoc]

theorem form_yx (hB : B.IsGood σ) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ} (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j)
    {x y : Fin n → E} (h : form σ J x y = 1) : form σ J y x = ((ε : ℤ) : E) := by
  have hs := PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm
  rw [← hs (form σ J y x), form_eps hs hJ, h, mul_one, map_intCast]

theorem decomp (hB : B.IsGood σ) {r s} (hX : X.IsHerm σ B r s) {H : Plane E n n₁} {i j} (hH : H.IsAdapted σ B X X₁ i j)
    (z : Fin n → AE F E) : ∃ (U : Fin n₁ → AE F E) (a : AE F E),
      z = incM F H.ι *ᵥ U + a • incV F H.x + cA σ (bA σ X.J (incV F H.x) z) • incV F H.y := by
  obtain ⟨ε, A', hF⟩ := isFr hB (Or.inl hX) hH
  obtain ⟨U, a, b, rfl⟩ := (IsFr.ad hF).span z
  refine ⟨U, a, ?_⟩
  congr 2
  have g := (IsFr.ad hF).gram
  have e : (fun i => cA σ ((fr (incM F H.ι) (incV F H.x) (incV F H.y) *ᵥ Sum.elim U ![a, b]) i)) =
      (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ fun i => cA σ (Sum.elim U ![a, b] i) :=
    funext fun i => RingHom.map_mulVec (cA σ : AE F E →+* AE F E) _ _ i
  have g2 := congrFun (congrArg (· *ᵥ fun i => cA σ (Sum.elim U ![a, b] i)) g) (Sum.inr 0)
  rw [← fr_mulVec, bA, e]
  have g3 : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ
      (fun i => cA σ (Sum.elim U ![a, b] i)) = cA σ b := by
    simp only [← Matrix.mulVec_mulVec] at g2
    refine Eq.trans ?_ (g2.trans ?_)
    · rfl
    · simp [gr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [g3, PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm]

end PositivityTheory.ThKG.Loc.Bump

end
end
end
