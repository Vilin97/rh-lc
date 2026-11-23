module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorHeightBound
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SumLeSqrtCardMul

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem card_support_le {R : Type*} [CommSemiring R] {D N n n' : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) (hu : UDegLE n' Q) :
    Q.support.card ≤
      (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) := by
  classical
  let fx : (UXVar D N →₀ ℕ) → (Fin (D + 2) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i))
  let fu : (UXVar D N →₀ ℕ) → (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))
  have hmaps : ∀ s ∈ Q.support, (fun s => (fx s, fu s)) s ∈
      (Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n') := by
    intro s hs
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
    constructor
    · simpa [fx, xDeg] using hx s hs
    · have := hu s hs
      simp only [fu, Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_option, Option.elim]
      unfold uDeg at this ⊢
      omega
  have hinj : Set.InjOn (fun s => (fx s, fu s)) Q.support := by
    intro s _ t _ hst
    simp only [Prod.mk.injEq] at hst
    ext v
    rcases v with p | i
    · have := congrArg (fun f => f (some p)) hst.2
      simpa [fu] using this
    · have := congrArg (fun f => f i) hst.1
      simpa [fx] using this
  calc Q.support.card ≤ ((Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n')).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = _ := by
      rw [Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
        Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_option, Fintype.card_prod]
      congr 1
      · rw [show D + 2 + n - 1 = n + D + 1 by omega]
        exact Nat.choose_symm_of_eq_add (by omega)
      · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega]
        exact Nat.choose_symm_of_eq_add (by omega)

noncomputable def Ey {D N : ℕ} (y : Fin (N + 1) → ℂ) :
    MvPolynomial (UXVar D N) ℂ →ₐ[ℂ] MvPolynomial (Fin (D + 2) × Fin (N + 1)) ℂ :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))

theorem sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (a : α → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  calc ∑ i ∈ s, a i ≤ |∑ i ∈ s, a i| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ s, a i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (s.card * ∑ i ∈ s, a i ^ 2) := Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _

theorem coeff_Ey_le {D N n n' : ℕ} (R : MvPolynomial (UXVar D N) ℂ) (hx : XHom n R)
    (hu : UDegLE n' R) (y : Fin (N + 1) → ℂ) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    ‖AddMonoidAlgebra.coeff (Ey y R) β‖ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R *
      Real.sqrt ((n + D + 1).choose (D + 1) *
        (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) * (∑ j, ‖y j‖) ^ n := by
  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality _ (Ey y R)).2 β
  set z := ReciprocityTheory.MultiplicativeHeights.torusPoint θ with hzdef
  have hz : ∀ p, ‖z p‖ = 1 := by
    intro p
    simp only [hzdef, ReciprocityTheory.MultiplicativeHeights.torusPoint]
    rw [Complex.norm_exp]
    simp
  set Y := ∑ j, ‖y j‖ with hY
  set pt : UXVar D N → ℂ := fun v => eval z (Sum.elim X (fun i => ∑ j, X (i, j) * C (y j)) v)
    with hpt
  have hev : eval z (Ey y R) = eval pt R := by
    have := congrArg (fun φ => φ R)
      (MvPolynomial.comp_aeval (R := ℂ) (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))
        (aeval z))
    simp only [AlgHom.comp_apply] at this
    calc eval z (Ey y R) = aeval z (Ey y R) := by simp
      _ = _ := this
      _ = eval pt R := by simp [hpt]
  have hpt1 : ∀ p, ‖pt (Sum.inl p)‖ = 1 := fun p => by simp [hpt, hz]
  have hpt2 : ∀ i, ‖pt (Sum.inr i)‖ ≤ Y := by
    intro i

    simp only [hpt, Sum.elim_inr, map_sum, map_mul, eval_X, eval_C]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, hz, one_mul]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono : ∀ α ∈ R.support, ‖∏ v, pt v ^ α v‖ ≤ Y ^ n := by
    intro α hα
    rw [norm_prod, Fintype.prod_sum_type]
    simp only [norm_pow, hpt1, one_pow, Finset.prod_const_one, one_mul]
    calc ∏ i, ‖pt (Sum.inr i)‖ ^ α (Sum.inr i) ≤ ∏ i, Y ^ α (Sum.inr i) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt2 i) _
      _ = Y ^ n := by rw [Finset.prod_pow_eq_pow_sum, ← hx α hα]; rfl
  have hcard := card_support_le R hx hu
  calc ‖AddMonoidAlgebra.coeff (Ey y R) β‖ ≤ ‖eval z (Ey y R)‖ := hθ
    _ = ‖∑ α ∈ R.support, AddMonoidAlgebra.coeff R α * ∏ v, pt v ^ α v‖ := by rw [hev, eval_eq']
    _ ≤ ∑ α ∈ R.support, ‖AddMonoidAlgebra.coeff R α‖ * Y ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono α hα) (norm_nonneg _)
    _ = (∑ α ∈ R.support, ‖AddMonoidAlgebra.coeff R α‖) * Y ^ n := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt R.support.card * ReciprocityTheory.MultiplicativeHeights.polyL2 R) * Y ^ n := by
        gcongr
        exact sum_le_sqrt_card_mul _ _
    _ ≤ _ := by
        rw [mul_comm (Real.sqrt _) (ReciprocityTheory.MultiplicativeHeights.polyL2 R)]
        gcongr
        unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffEvWMem

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}

noncomputable def evW (w : Fin (N + 1) → B) :
    MvPolynomial (UXVar D N) R →ₐ[R] MvPolynomial (Fin (D + 2) × Fin (N + 1)) B :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (w j))

def CoeffIn (W : Submodule R B) (m : ℕ) (p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) : Prop :=
  ∀ β, AddMonoidAlgebra.coeff p β ∈ W ^ m

variable (W : Submodule R B)

theorem coeffIn_mul {m m' : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m' q) : CoeffIn W (m + m') (p * q) := fun β => by
  rw [coeff_mul, pow_add]
  exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hp _) (hq _)

theorem coeffIn_one : CoeffIn W 0 (1 : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [pow_zero, coeff_one]
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_pow {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (k : ℕ) : CoeffIn W (m * k) (p ^ k) := by
  induction k with
  | zero => simpa using coeffIn_one W
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact coeffIn_mul W ih hp

theorem coeffIn_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin (D + 2) × Fin (N + 1)) B)
    (m : ι → ℕ) (h : ∀ i ∈ s, CoeffIn W (m i) (p i)) : CoeffIn W (∑ i ∈ s, m i) (∏ i ∈ s, p i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using coeffIn_one W) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact coeffIn_mul W (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem coeffIn_smul {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (r : R) : CoeffIn W m (C (algebraMap R B r) * p) := fun β => by
  rw [coeff_C_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hp β)

theorem coeffIn_X (u : Fin (D + 2) × Fin (N + 1)) : CoeffIn W 0 (X u : MvPolynomial _ B) := fun β => by
  rw [pow_zero, coeff_X']
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_lin (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) (i : Fin (D + 2)) :
    CoeffIn W 1 (∑ j, X (i, j) * C (w j) : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [coeff_sum, pow_one]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X']
  split_ifs
  · rw [mul_one]
    exact hw j
  · rw [mul_zero]
    exact zero_mem _

private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

theorem coeffIn_evW (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) {n : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) : CoeffIn W n (evW w Q) := by
  intro β

  rw [Q.as_sum, map_sum, coeff_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hterm : CoeffIn W n (evW w (monomial s (AddMonoidAlgebra.coeff Q s))) := by
    rw [evW, aeval_monomial, MvPolynomial.algebraMap_apply]
    apply coeffIn_smul
    rw [Finsupp.prod, ← hx s hs, ← sum_support_inr_eq_xDeg s]
    refine coeffIn_prod W s.support _ _ fun x _ => ?_
    cases x with
    | inl p => simpa using coeffIn_pow W (coeffIn_X W p) (s (Sum.inl p))
    | inr i => simpa using coeffIn_pow W (coeffIn_lin W w hw i) (s (Sum.inr i))
  exact hterm β

theorem coeff_evW_mem (w : Fin (N + 1) → B) {n : ℕ} (Q : MvPolynomial (UXVar D N) R)
    (hx : XHom n Q) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (evW w Q) β ∈
      Submodule.span R (Set.range fun s : Fin n → Fin (N + 1) => ∏ k, w (s k)) := by
  have h := coeffIn_evW (Submodule.span R (Set.range w)) w (fun j => Submodule.subset_span ⟨j, rfl⟩) Q hx β
  rw [Submodule.span_pow] at h
  refine Submodule.span_mono ?_ h
  intro a ha
  rw [Set.mem_pow] at ha
  obtain ⟨f, rfl⟩ := ha
  choose s hs using fun k => (f k).2
  refine ⟨s, ?_⟩
  show ∏ k, w (s k) = _
  rw [List.prod_ofFn]
  exact Finset.prod_congr rfl fun k _ => hs k

end

theorem evW_factor {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] [Algebra S B] [IsScalarTower R S B] {D N n : ℕ} (y : Fin (N + 1) → S) (w0 : B)
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) :
    evW (fun j => algebraMap S B (y j) * w0) Q =
      MvPolynomial.map (algebraMap S B) (evW y Q) * C (w0 ^ n) := by

  rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [evW, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul, map_C, Finsupp.prod,
    map_prod, map_pow]
  rw [← IsScalarTower.algebraMap_apply, mul_assoc]
  congr 1
  rw [← hx s hs, ← sum_support_inr_eq_xDeg s]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases x with
  | inl p => simp
  | inr i =>

    simp only [Sum.elim_inr, map_sum, map_mul, map_X, map_C]
    rw [← mul_pow, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem map_evW_eq {K S : Type*} [Field K] [CommRing S] [Algebra K S] {D N : ℕ} (P : S →+* ℂ)
    (sg : K →+* ℂ) (hP : P.comp (algebraMap K S) = sg) (y : Fin (N + 1) → S)
    (R : MvPolynomial (UXVar D N) K) :
    MvPolynomial.map P (evW (R := K) y R) = Ey (fun j => P (y j)) (MvPolynomial.map sg R) := by
  have h : (MvPolynomial.map P).comp (evW (R := K) (D := D) y).toRingHom =
      (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evW, Ey, ← hP]
    · intro i
      cases i <;> simp [evW, Ey]
  exact RingHom.congr_fun h R

end ReciprocityTheory.ChartRestriction.G.T0
end
end
