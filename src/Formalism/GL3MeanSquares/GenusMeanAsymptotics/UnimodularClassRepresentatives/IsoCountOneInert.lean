module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MapMkConjTranspose
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardMapEquiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSubMemOfInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns

open Matrix

variable {k : Type*} [Field k]

def cj {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) : Matrix n' n k := (X.map σ).transpose

theorem cj_apply {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) (i : n') (j : n) :
    cj σ X i j = σ (X j i) := rfl

theorem cj_mul {n n' n'' : Type*} [Fintype n'] (σ : k ≃+* k) (X : Matrix n n' k)
    (Y : Matrix n' n'' k) : cj σ (X * Y) = cj σ Y * cj σ X := by
  ext i j
  simp [cj_apply, Matrix.mul_apply, mul_comm]

theorem cj_one {n : Type*} [DecidableEq n] (σ : k ≃+* k) : cj σ (1 : Matrix n n k) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cj_apply]
  · simp [cj_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem exists_refl {n : Type*} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (x y : n → k) (hx : ∑ i, σ (x i) * x i = 1)
    (hy : ∑ i, σ (y i) * y i = 1) (hxy : ∑ i, σ (y i) * x i ≠ 1) :
    ∃ g : Matrix n n k, cj σ g * g = 1 ∧ g *ᵥ x = y := by
  set u : n → k := x - y with hu
  set a : k := ∑ i, σ (u i) * x i with ha
  have ha1 : a = 1 - ∑ i, σ (y i) * x i := by
    simp only [ha, hu, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib, hx]
  have ha0 : a ≠ 0 := by
    rw [ha1]; exact sub_ne_zero.mpr (Ne.symm hxy)
  have hsa0 : σ a ≠ 0 := by simpa using ha0
  have hsa : σ a = 1 - ∑ i, σ (x i) * y i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha1]; simp [map_sum, hσ, mul_comm]
  have hn : ∑ i, σ (u i) * u i = a + σ a := by
    rw [hsa, ha1]
    simp only [hu, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib, hx, hy]
    ring
  set P : Matrix n n k := vecMulVec u (fun i => σ (u i)) with hP
  have hPP : P * P = (a + σ a) • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec, ← hn]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
    ring
  have hcP : cj σ P = P := by
    ext i j
    simp [cj_apply, hP, vecMulVec_apply, hσ, mul_comm]
  refine ⟨1 - a⁻¹ • P, ?_, ?_⟩
  · have hc : cj σ (1 - a⁻¹ • P) = 1 - (σ a)⁻¹ • P := by
      ext i j
      have := congrFun (congrFun hcP i) j
      have h1 := congrFun (congrFun (cj_one (n := n) σ) i) j
      simp only [cj_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
        map_inv₀] at this h1 ⊢
      rw [this, h1]
    rw [hc, sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
    have : (σ a)⁻¹ * a⁻¹ * (a + σ a) = a⁻¹ + (σ a)⁻¹ := by
      field_simp
      ring
    rw [smul_smul, this, add_smul]
    abel
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP, Matrix.vecMulVec_mulVec]
    have : (fun i => σ (u i)) ⬝ᵥ x = a := rfl
    rw [this]
    ext i
    simp [hu, ha0]

theorem cj_cj {n n' : Type*} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (X : Matrix n n' k) :
    cj σ (cj σ X) = X := by
  ext i j
  simp [cj_apply, hσ]

theorem exists_col {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (x : Fin (m + 1) → k) (hx : ∑ i, σ (x i) * x i = 1) :
    ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) k, cj σ g * g = 1 ∧ ∀ i, g i 0 = x i := by
  have he : ∑ i, σ ((Pi.single 0 1 : Fin (m + 1) → k) i) * (Pi.single 0 1 : Fin (m + 1) → k) i = 1 := by
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  have hs : ∀ y : Fin (m + 1) → k, ∑ i, σ (y i) * (Pi.single 0 1 : Fin (m + 1) → k) i = σ (y 0) := by
    intro y
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  by_cases h1 : σ (x 0) = 1
  · obtain ⟨t, ht⟩ := hne
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht
    have hst0 : σ t ≠ 0 := by simpa using ht0
    set ζ : k := σ t / t with hζ
    have hζ0 : ζ ≠ 0 := div_ne_zero hst0 ht0
    have hsζ : σ ζ = t / σ t := by simp [hζ, hσ]
    have hN : σ ζ * ζ = 1 := by
      rw [hsζ, hζ]; field_simp
    have hsζ1 : σ ζ ≠ 1 := by
      rw [hsζ]
      intro h
      rw [div_eq_one_iff_eq hst0] at h
      exact ht h.symm
    obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) (fun i => ζ * x i) he
      (by
        have : ∀ i, σ (ζ * x i) * (ζ * x i) = (σ ζ * ζ) * (σ (x i) * x i) := by
          intro i; rw [map_mul]; ring
        simp only [this, ← Finset.mul_sum, hx, hN, mul_one])
      (by rw [hs, map_mul, h1, mul_one]; exact hsζ1)
    refine ⟨ζ⁻¹ • g, ?_, ?_⟩
    · have hc : cj σ (ζ⁻¹ • g) = (σ ζ)⁻¹ • cj σ g := by
        ext i j
        simp [cj_apply]
      rw [hc, smul_mul_smul_comm, hg, ← mul_inv, hN, inv_one, one_smul]
    · intro i
      have := congrFun hgx i
      rw [Matrix.mulVec_single_one] at this
      simp only [Matrix.col_apply] at this
      simp [this, hζ0]
  · obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) x he hx (by rw [hs]; exact h1)
    refine ⟨g, hg, fun i => ?_⟩
    have := congrFun hgx i
    rw [Matrix.mulVec_single_one] at this
    simpa using this

def emb {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i

theorem one_succ_succ {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j.succ = (1 : Matrix (Fin m) (Fin m) k) i j := by
  simp [Matrix.one_apply]

theorem emb_unitary {m : ℕ} (σ : k ≃+* k) (Y : Matrix (Fin m) (Fin m) k) (h : cj σ Y * Y = 1) :
    cj σ (emb Y) * emb Y = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [emb, Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]
  · simp [emb, Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, (Fin.succ_ne_zero j').symm]
  · simp [emb, Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, Fin.succ_ne_zero i']
  · have := congrFun (congrFun h i') j'
    rw [one_succ_succ, ← this]
    simp [emb, Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]

theorem eq_emb {m : ℕ} (σ : k ≃+* k) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : cj σ Z * Z = 1) (h0 : Z 0 0 = 1) (hs : ∀ i : Fin m, Z i.succ 0 = 0) :
    Z = emb (Z.submatrix Fin.succ Fin.succ) ∧
      cj σ (Z.submatrix Fin.succ Fin.succ) * Z.submatrix Fin.succ Fin.succ = 1 := by
  have hrow : ∀ j : Fin m, Z 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun h 0) j.succ
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, h0, hs, Matrix.one_apply,
      (Fin.succ_ne_zero j).symm] using this
  constructor
  · ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [emb, h0]
    · simp [emb, hrow]
    · simp [emb, hs]
    · simp [emb]
  · ext i j
    have := congrFun (congrFun h i.succ) j.succ
    rw [one_succ_succ] at this
    rw [← this]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, hrow]

theorem card_succ {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} =
      Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} *
        Nat.card {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} := by
  choose g hg hgc using fun x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} =>
    exists_col σ hσ hne x.1 x.2
  have hg' : ∀ x, g x * cj σ (g x) = 1 := fun x => mul_eq_one_comm.mp (hg x)
  have hcol : ∀ x (Y : Matrix (Fin m) (Fin m) k) i, (g x * emb Y) i 0 = x.1 i := by
    intro x Y i
    simp [emb, Matrix.mul_apply, Fin.sum_univ_succ, hgc]
  let Φ : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} ×
      {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} →
      {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} := fun p =>
    ⟨g p.1 * emb p.2.1, by
      rw [cj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cj σ (g p.1)), hg, Matrix.one_mul]
      exact emb_unitary σ _ p.2.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨x, Y⟩ ⟨x', Y'⟩ h
      have h1 : g x * emb Y.1 = g x' * emb Y'.1 := congrArg Subtype.val h
      have hxx : x = x' := by
        apply Subtype.ext
        funext i
        rw [← hcol x Y.1 i, h1, hcol]
      subst hxx
      have h2 : emb Y.1 = emb Y'.1 := by
        have := congrArg (fun M => cj σ (g x) * M) h1
        simpa only [← Matrix.mul_assoc, hg, Matrix.one_mul] using this
      have hYY : Y = Y' := by
        apply Subtype.ext
        ext i j
        exact congrFun (congrFun h2 i.succ) j.succ
      rw [hYY]
    · rintro ⟨X, hX⟩
      have hx : ∑ i, σ (X i 0) * X i 0 = 1 := by
        have := congrFun (congrFun hX 0) 0
        simpa [Matrix.mul_apply, cj_apply] using this
      set x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} := ⟨fun i => X i 0, hx⟩ with hxdef
      set Z := cj σ (g x) * X with hZ
      have hZu : cj σ Z * Z = 1 := by
        rw [hZ, cj_mul, cj_cj σ hσ, Matrix.mul_assoc, ← Matrix.mul_assoc (g x), hg',
          Matrix.one_mul, hX]
      have hZc : ∀ i, Z i 0 = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i 0 := by
        intro i
        rw [← hg x, hZ]
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hgc x l]
      obtain ⟨hE, hU⟩ := eq_emb σ Z hZu (by rw [hZc]; simp)
        (fun i => by rw [hZc]; simp [Fin.succ_ne_zero i])
      refine ⟨(x, ⟨_, hU⟩), Subtype.ext ?_⟩
      change g x * emb (Z.submatrix Fin.succ Fin.succ) = X
      rw [← hE, hZ, ← Matrix.mul_assoc, hg', Matrix.one_mul]
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns

namespace Formalism.HermitianLattices.Ext.L3

theorem card_unitary_fin {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) (m : ℕ) :
    (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) =
      (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (-(q : ℝ))⁻¹ ^ j) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have h1 : 0 < Fintype.card k := Fintype.card_pos
    rw [hq] at h1
    have : q ≠ 0 := by
      rintro rfl
      simp at h1
    exact_mod_cast this
  induction m with
  | zero =>
    have : Nat.card {X : Matrix (Fin 0) (Fin 0) k // (X.map σ).transpose * X = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨1, Subsingleton.elim _ _⟩⟩⟩
    rw [this]
    simp
  | succ m ih =>
    have h1 := FiniteUnitaryColumns.card_succ (m := m) σ hσ hne
    have h2 := card_herm_norm_eq σ hσ hne q hq (m + 1) (by omega) 1 (map_one σ) one_ne_zero
    have h2' : (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) =
        (q : ℝ) ^ m * ((q : ℝ) ^ (m + 1) - (-1) ^ (m + 1)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h2
      simpa using this
    have h1' : (Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k //
        (X.map σ).transpose * X = 1} : ℝ) =
        (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) *
          (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) := by
      exact_mod_cast h1
    rw [h1', h2', ih, Finset.prod_Icc_succ_top (by omega)]
    have h3 : (q : ℝ) ^ ((m + 1) ^ 2) = (q : ℝ) ^ (m ^ 2) * ((q : ℝ) ^ m * (q : ℝ) ^ (m + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    have h4 : (q : ℝ) ^ (m + 1) * (1 - (-(q : ℝ))⁻¹ ^ (m + 1)) =
        (q : ℝ) ^ (m + 1) - (-1) ^ (m + 1) := by
      have : (-(q : ℝ))⁻¹ = (-1) * (q : ℝ)⁻¹ := by
        rw [neg_mul, one_mul, inv_neg]
      rw [this, mul_pow, mul_sub, mul_one, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hq0, one_pow,
        mul_one]
    rw [h3, ← h4]
    ring

theorem card_GL_fin {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q) (m : ℕ) :
    (Nat.card (GL (Fin m) k) : ℝ) = (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (q : ℝ)⁻¹ ^ j) := by
  subst hq
  set q : ℕ := Fintype.card k with hqd
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hq0 : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  rw [Matrix.card_GL_field, Fin.prod_univ_eq_prod_range (fun i => q ^ m - q ^ i) m, Nat.cast_prod]
  have h1 : ∀ i ∈ Finset.range m, ((q ^ m - q ^ i : ℕ) : ℝ) =
      (q : ℝ) ^ m * (1 - (q : ℝ)⁻¹ ^ (m - 1 - i + 1)) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq1 him.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have : m = i + (m - 1 - i + 1) := by omega
    conv_rhs => rw [this, pow_add]
    have h5 : m - 1 - i + 1 = i + (m - 1 - i + 1) - 1 - i + 1 := by omega
    rw [← h5, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, ← sq, Finset.prod_range_reflect (fun j => 1 - (q : ℝ)⁻¹ ^ (j + 1)) m]
  congr 1
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun j => 1 - (q : ℝ)⁻¹ ^ j) 0 m 1]
  rfl

end Formalism.HermitianLattices.Ext.L3
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsoCountOneInert

section

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem isoCount_one_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - (-(Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  have e1 : extP K 𝔭 ^ 1 = P := by
    rw [pow_one]
    exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP
      (by rw [← conjIdeal_eq_comap]; exact hc) hθ
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]
  have hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x := NormResidues.sigHom_sigHom P hc
  have hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x := by
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [NormResidues.sigEquiv_mk] at h
    exact Ideal.Quotient.eq.1 h.symm
  have h1 := UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]
      rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))
    (by
      intro i
      rw [star_mk, star_def, hu])
    (fun i => isUnit_mk (hunit i) 1)
  unfold isoCount
  rw [diagonal_map (map_zero _), h1]
  exact card_unitary_fin _ hσ hne _ hq m

theorem isoCount_one_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - ((Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have e1 : extP K 𝔭 ^ 1 ≤ P := by
    rw [pow_one]
    exact Ideal.map_comap_le
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := finite_quot (K := K) h𝔭 1
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]
  have hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 =>
      (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a) := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro y
      obtain ⟨z, hz⟩ := NormResidues.pairHom_surjective hP hc y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      rw [← hz, NormResidues.pairHom_apply]
      show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _
      rw [star_mk]
      rfl
    · rw [absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]
      apply le_of_eq
      ring
  have h1 := UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb
    ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)))
    (by
      rw [map_mk_conjTranspose, diagonal_conjTranspose]
      congr 2
      funext i
      exact hu i)
    (by
      rw [diagonal_map (map_zero _), det_diagonal]
      exact Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
        (fun i _ => isUnit_mk (hunit i) 1))
  unfold isoCount
  rw [h1]
  exact card_GL_fin _ hq m

theorem isoCount_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, ite_eq_left hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, ite_eq_right hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]

theorem isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end
end
