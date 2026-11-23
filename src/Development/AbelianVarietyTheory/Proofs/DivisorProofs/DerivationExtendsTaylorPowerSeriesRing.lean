module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
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
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPowStatement
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSingleDerivationTaylorPowerSeries

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem list_foldr_iterate_single_of_nodup {A : Type} {n : ℕ} (d : Fin n → A → A) (j : Fin n) (f : A) :
    ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun i g => (d i)^[(Finsupp.single j 1 : Fin n →₀ ℕ) i] g) f = if j ∈ l then d j f else f := by
  intro l hl
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hij : i = j
    · subst hij
      simp [hl.1]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Finsupp.single_apply, hij, hji]

theorem taylor_coeff_single (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  have hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f := by
    unfold iterOp
    rw [list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]
    simp [List.mem_finRange]
  have hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _
  rw [hit, hprod, inv_one, one_smul]

end GlobalTheory.FormalOrigin.Extend
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSingleDerivationTaylorPowerSeriesStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.coeff_single_derivationTaylorPowerSeries : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A), MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | exact GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | (intros; apply GlobalTheory.FormalOrigin.Extend.taylor_coeff_single <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConst

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

open Matrix

theorem powerSeries_matrix_solve : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  intro n R _ J hJ b
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R) := Matrix.of J
  have hM : (MvPowerSeries.constantCoeff (σ := Fin n) (R := R)).mapMatrix M = 1 := by
    ext i j
    simp [M, Matrix.one_apply, hJ]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨M⁻¹ *ᵥ b, fun i => ?_⟩
  have h := congrFun (Matrix.mulVec_mulVec b M M⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConstStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  first | exact @GlobalTheory.powerSeries_matrix_solve | exact GlobalTheory.powerSeries_matrix_solve | (intros; apply GlobalTheory.powerSeries_matrix_solve <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLe

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem filt_mul_filt_le (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ) :
    filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  classical
  refine Ideal.mul_le.2 fun F hF G hG => ?_
  rw [mem_filt] at hF hG ⊢
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hα : p.1 + p.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : α.degree = p.1.degree + p.2.degree := by rw [← hα, map_add (f := _)]
  have h := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.FormalOrigin.Extend
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLeStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le : ∀ (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ), filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | exact GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | (intros; apply GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing

section

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

noncomputable def pdZ {σ R : Type} [CommRing R] (j : σ) : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := MvPowerSeries.pderiv (R := R) j
  map_add' := map_add _
  map_smul' m x := by simpa using map_zsmul (MvPowerSeries.pderiv (R := R) j) m x
  map_one_eq_zero' := MvPowerSeries.pderiv_one
  leibniz' := (MvPowerSeries.pderiv (R := R) j).leibniz

theorem pdZ_apply {σ R : Type} [CommRing R] (j : σ) (F : MvPowerSeries σ R) :
    pdZ j F = MvPowerSeries.pderiv (R := R) j F := rfl

theorem add_sum_apply {σ R ι : Type} [CommRing R] [Fintype ι] (E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (G : ι → MvPowerSeries σ R) (P : ι → Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (F : MvPowerSeries σ R) : (E + ∑ j, G j • P j) F = E F + ∑ j, G j * P j F := by
  rw [Derivation.add_apply]
  congr 1

  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  change ∑ j, (G j • P j) F = ∑ j, G j * P j F
  simp [Derivation.smul_apply, smul_eq_mul]

theorem derivation_extends : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  intro R A _ _ _ _ _ _ _ _ inc ev hev n ds z hz hdz hm hinc d D hdD
  obtain ⟨T, hT⟩ := taylor_isRingHom A R n ev ds
  simp only [← hT]
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries (Fin n) R D
  have hEC : ∀ r, E (MvPowerSeries.C r) = MvPowerSeries.C (D r) := by
    intro r; ext α
    rw [hE, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
    split_ifs <;> simp
  have hTinc : ∀ r, T (inc r) = MvPowerSeries.C r := by
    intro r; rw [hT, taylor_const A R n ev ds (inc r) (fun i => hinc i r), hev]
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const n R (fun i j => pdZ j (T (z i))) (by
    intro i j
    simp only [pdZ_apply]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add, hT,
      GlobalTheory.T.coeff_single_derivationTaylorPowerSeries, hdz]
    simp [eq_comm]) (fun i => T (d (z i)) - E (T (z i)))
  set dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) := E + ∑ j, G j • pdZ j with hdΩ
  have hΩ : ∀ F, dΩ F = E F + ∑ j, G j * pdZ j F := fun F => add_sum_apply E G _ F
  refine ⟨dΩ, fun r => ?_, ?_⟩
  · simp [hΩ, hEC, pdZ_apply]
  ·
    set e : A → MvPowerSeries (Fin n) R := fun f => dΩ (T f) - T (d f) with he
    have e_add : ∀ f g, e (f + g) = e f + e g := by
      intro f g; simp only [he, map_add (f := _)]; ring
    have e_mul : ∀ f g, e (f * g) = T f * e g + T g * e f := by
      intro f g; simp only [he, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]; ring
    have e_neg : ∀ f, e (-f) = - e f := by
      intro f; simp only [he, map_neg]; ring
    have e_one : e 1 = 0 := by simp [he]
    let Q : Subring A :=
      { carrier := {f | e f = 0}
        mul_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_mul, hf, hg]; ring
        one_mem' := e_one
        add_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_add, hf, hg]; ring
        zero_mem' := by simp [he]
        neg_mem' := fun {f} hf => by simp only [Set.mem_setOf_eq] at *; rw [e_neg, hf, neg_zero] }
    have hQ : Subring.closure (Set.range inc ∪ Set.range z) ≤ Q := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | ⟨i, rfl⟩)
      · change e (inc r) = 0
        simp [he, hTinc, hdD, hΩ, hEC, pdZ_apply]
      · change e (z i) = 0
        have := hG i
        simp only [he, hΩ]
        rw [this]; ring

    have hc0 : ∀ x, MvPowerSeries.constantCoeff (T x) = ev x := by
      intro x
      rw [hT, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      change (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp _ 0 x) = _
      rw [iterOp_zero]; simp
    have hloc : ∀ x ∈ maximalIdeal A, ev x ∈ maximalIdeal R := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : x - inc (ev x) ∈ maximalIdeal A := by
        apply le_maximalIdeal (RingHom.ker_ne_top ev)
        rw [RingHom.mem_ker, map_sub, hev, sub_self]
      have h2 : inc (ev x) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ hx h1
      exact (mem_maximalIdeal _).1 h2 (hu.map inc)
    have hT1 : ∀ x ∈ maximalIdeal A, T x ∈ filt (maximalIdeal R) 1 := by
      intro x hx α
      by_cases hα : α = 0
      · subst hα
        simp only [map_zero, Nat.sub_zero, pow_one]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc0]
        exact hloc x hx
      · have : 1 - α.degree = 0 := by
          have : α.degree ≠ 0 := by
            intro h0; exact hα ((Finsupp.degree_eq_zero_iff α).1 h0)
          omega
        rw [this, pow_zero, Ideal.one_eq_top]; trivial
    have hTk : ∀ k, ∀ x ∈ maximalIdeal A ^ k, T x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [map_mul, add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb
    have hek : ∀ k, ∀ x ∈ maximalIdeal A ^ (k + 1), e x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [e_mul]
          refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (hTk _ b hb))
          rw [add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [e_add]; exact Ideal.add_mem _ ha hb
    intro f
    have : e f = 0 := by
      refine eq_zero_of_forall_mem_filt (maximalIdeal R) _ fun k => ?_
      obtain ⟨p, hp, hfp⟩ := GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow R A inc ev hev n z hm (k + 1) f
      have h1 : e f = e p + e (f - p) := by rw [← e_add]; congr 1; ring
      rw [h1, show e p = 0 from hQ hp, zero_add]
      exact hek k _ hfp
    exact sub_eq_zero.1 this

end GlobalTheory.FormalOrigin.Extend
end
end
