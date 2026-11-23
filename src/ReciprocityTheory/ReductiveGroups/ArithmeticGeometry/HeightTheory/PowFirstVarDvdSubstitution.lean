module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow
import Mathlib.Algebra.MvPolynomial.Division
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RelationMapCommTransvection

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

noncomputable def trv {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) :
    MvPolynomial (TVar D N) R →ₐ[R] Polynomial (MvPolynomial (TVar D N) R) :=
  aeval fun t => if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2)) else Polynomial.C (X t)

theorem trv_X {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) (t : TVar D N) :
    trv i k e (X t) = if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2))
      else Polynomial.C (X t) := by
  unfold trv
  rw [MvPolynomial.aeval_X]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem relation_map_comm_transvection (c : ι) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    (Polynomial.mapRingHom (d.relationEliminateColumn c).toRingHom).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := Ω c) i k Polynomial.X).toRingHom.comp (d.relationEliminateColumn c).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [trv, Data.relationEliminateColumn]
  · rintro ⟨a, b⟩
    have hC : ∀ x : Ω c, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (C x) = Polynomial.C (C x) := by
      intro x
      simp [trv, Polynomial.algebraMap_apply]
    have hX : ∀ r l, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all
    have hXK : ∀ r l, trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all

    set φ : Fin (d.D + 1) → MvPolynomial (TVar d.D d.N) (Ω c) := fun r => d.relationEliminateColumn c (X (r, b)) with hφ
    have hφtrv : ∀ r, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ r) =
        Polynomial.C (φ r) + (if r = i then Polynomial.X * Polynomial.C (φ k) else 0) := by
      intro r
      by_cases h2 : b = d.jc c
      · have e1 : ∀ r', φ r' = -∑ l ∈ Finset.univ.erase (d.jc c),
            X (r', l) * C (ratio (Ω := Ω c) (d.w l c) (d.w (d.jc c) c)) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, eq_self_iff_true, if_true]

        rw [e1 r, e1 k, map_neg, map_sum]
        by_cases h1 : r = i

        · simp only [h1, eq_self_iff_true, if_true, map_mul, hX, hC, map_neg, map_sum, add_mul,
          Finset.sum_add_distrib, mul_neg, Finset.mul_sum, mul_assoc, neg_add]

        · simp only [h1, if_false, add_zero, map_mul, hX, hC, map_neg, map_sum]
      · have e1 : ∀ r', φ r' = X (r', b) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, if_false]
        rw [e1 r, e1 k, hX]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_mapRingHom]
    rw [hXK a b]
    change _ = trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ a)
    rw [hφtrv a]
    by_cases h1 : a = i
    · simp only [h1, eq_self_iff_true, if_true, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X]
      rfl
    · simp only [h1, if_false, add_zero, Polynomial.map_C]
      rfl

theorem transvection_fix_generator (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    trv i k Polynomial.X F0 = Polynomial.C F0 := by
  classical
  have h1 : ∀ n, F0 ∣ (trv i k Polynomial.X F0).coeff n := fun n => (hker _).1 (by
    have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n)
      (congrArg (fun f => f F0) (d.relation_map_comm_transvection c i k hik))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h2
    rw [h2, (hker F0).2 dvd_rfl, map_zero, Polynomial.coeff_zero])
  obtain ⟨R, hR⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 h1
  let Ψ : Polynomial (KTp K d.D d.N) →+* Polynomial (KTp K d.D d.N) :=
    Polynomial.eval₂RingHom (trv i k (-Polynomial.X)).toRingHom Polynomial.X
  have hΨ : Ψ.comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [Ψ, trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X, Ψ]
      split_ifs with h
      · simp [trv_X, h, Ne.symm hik]
      · simp [trv_X, h]
  have hneg : (Polynomial.compRingHom (-Polynomial.X)).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := K) (D := d.D) (N := d.N) i k (-Polynomial.X)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
      split_ifs <;> simp
  have hC0 : (Polynomial.C F0 : Polynomial (KTp K d.D d.N)) ≠ 0 := by simpa using hF0
  have h3 : Polynomial.C F0 = Polynomial.C F0 * (R.comp (-Polynomial.X) * Ψ R) := by
    have e1 := congrArg (fun f => f F0) hΨ
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e1
    rw [hR, map_mul] at e1
    have e2 : Ψ (Polynomial.C F0) = trv i k (-Polynomial.X) F0 := by simp [Ψ]
    have e3 := congrArg (fun f => f F0) hneg
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_compRingHom_apply, hR, Polynomial.mul_comp, Polynomial.C_comp] at e3
    rw [e2, ← e3] at e1
    rw [← mul_assoc]; exact e1.symm
  have h4 : R.comp (-Polynomial.X) * Ψ R = 1 := (mul_left_cancel₀ hC0 (h3.symm.trans (mul_one _).symm))
  obtain ⟨u, hu, hu'⟩ := Polynomial.isUnit_iff.1 (isUnit_iff_exists_inv.2 ⟨_, h4⟩)
  have hRu : R = Polynomial.C u := by
    have e : (R.comp (-Polynomial.X)).comp (-Polynomial.X) = R := by
      rw [Polynomial.comp_assoc]; simp
    rw [← e, ← hu', Polynomial.C_comp]
  have h5 : (trv (R := K) i k Polynomial.X F0).eval 0 = F0 := by
    have : (Polynomial.evalRingHom 0).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [trv, MvPolynomial.algebraMap_eq]
      · rintro ⟨i', j⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
        split_ifs <;> simp
    exact congrArg (fun f => f F0) this
  rw [hR, hRu, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C] at h5
  have hu1 : u = 1 := mul_left_cancel₀ hF0 (h5.trans (mul_one F0).symm)
  rw [hR, hRu, hu1, map_one, mul_one]

theorem aeval_trv (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : S) :
    aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) F0 = aeval r F0 := by

  set ev : Polynomial (MvPolynomial (TVar d.D d.N) K) →+* S :=
    Polynomial.eval₂RingHom (aeval r : MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom b with hev
  have hcomp : ev.comp (trv (R := K) i k Polynomial.X).toRingHom =
      (aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) :
        MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hev, trv]
    · intro t
      by_cases h1 : t.1 = i <;> simp [hev, trv, h1] <;> ring
  have h := congrArg (fun φ => φ F0) hcomp
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [← h, transvection_fix_generator d c F0 hF0 hker i k hik]
  simp [hev]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PowFirstVarDvdSubstitution

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]

  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by
  classical
  revert hks
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hks
  have hik : i ≠ k := fun h => hks (h ▸ Finset.mem_insert_self _ _)
  have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
  rw [← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik
    (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]
  congr 2
  funext t
  by_cases h1 : t.1 = i
  · simp [h1, hi, hks']
  · simp [h1, Finset.mem_insert]

theorem pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by
  classical
  let S := FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
  let φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S :=
    IsScalarTower.toAlgHom K _ S
  have hφ : Function.Injective φ := IsFractionRing.injective _ S
  let x : Fin (d.D + 2) → S := fun i => φ (X (Sum.inr i))
  let U : Fin (d.D + 2) → Fin (d.N + 1) → S := fun a j => φ (X (Sum.inl (a, j)))
  have hx : ∀ i, x i ≠ 0 := fun i h0 => X_ne_zero (R := K)
    (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))
  have hx1 := hx 1
  let r : TVar d.D d.N → S := fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2
  have hG : φ (bilinearSubstitution F0) = aeval r F0 := by
    rw [bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t; simp [r, x, U]
  let s : Finset (Fin (d.D + 1)) := Finset.univ.erase 0
  have hs : s.card = d.D := by simp [s, Finset.card_erase_of_mem]
  let W : TVar d.D d.N → S := fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2
  have e1 := d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))
  have hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) =
      fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t)
        else (if t.1 ∈ s then W t else r t) := by
    funext t
    split_ifs
    · simp only [r, W, Fin.succ_zero_eq_one]
      linear_combination (x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1
    · rfl
  rw [hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs] at e1
  have e2 := aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)
  rw [hs] at e2
  let P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K := fun t =>
    if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2))
    else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))
  have hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t)
      else (if t.1 ∈ s then W t else r t)) F0 := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t
    simp only [P]
    split_ifs
    · simp only [map_sub, map_mul, W, x, U]
      simp only [x] at hx1
      linear_combination (φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1
    · simp [r, x, U]
  have key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)
    rw [hG, ← e1, hP, e2]; ring
  have key' := hφ key
  have hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :=
    MvPolynomial.X_prime
  have hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣
      X (Sum.inr 1) ^ (d.D * d0) := by
    intro h
    obtain ⟨q, hq⟩ := hp.dvd_of_dvd_pow h
    have := congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq
    simp at this
  exact hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end
