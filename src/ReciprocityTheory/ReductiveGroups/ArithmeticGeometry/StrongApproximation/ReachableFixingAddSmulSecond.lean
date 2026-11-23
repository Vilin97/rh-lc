module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichAlongSub
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.UnitaryTransvectionZeroSecondMemClosure

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.ConjMemEichSet

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

theorem tor_conj_e {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
    {l m c : K} {u : ι → K} (hml : m * σ l = 1) (hue : hf σ J u e = 0) (huf : hf σ J u f = 0) :
    tor σ J e f l m * eich σ J e u c = eich σ J e (σ l • u) (l * σ l * c) * tor σ J e f l m := by
  have hfe := hf_fe hσ hJ he hff hef
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ, hue, map_zero]
  have hfu : hf σ J f u = 0 := by rw [← hf_symm hσ hJ, huf, map_zero]
  rw [ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, eich_mulVec, tor_mulVec, tor_mulVec, eich_mulVec]
  simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hσ, he, hff, hef, hfe, hue, huf,
    heu, hfu, mul_zero, mul_one, add_zero, sub_zero, zero_add]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(hf σ J x e * u i) - l * c * hf σ J x e * e i) * hml

theorem conj_mem_along {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
    (hef : hf σ J e f = 1) {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichAlong σ J e f) :
    ∃ M' ∈ eichAlong σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨_, ⟨σ l • u, l * σ l * c, ?_, ?_, ?_, rfl⟩, tor_conj_e hσ hJ he hff hef hml hue huf⟩
  · rw [hf_smul_left, hue, mul_zero]
  · rw [hf_smul_left, huf, mul_zero]
  · rw [hf_smul_left, hf_smul_right, map_mul, map_mul, hσ]
    linear_combination (l * σ l) * hc

variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef

theorem conj_mem_eichSet {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichSet σ J e f) :
    ∃ M' ∈ eichSet σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  rcases hM with hM | hM
  · obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ he hff hef hml hM
    exact ⟨M', Or.inl h1, h2⟩
  · have hfe := hf_fe hσ hJ he hff hef
    have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
    obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ hff he hfe hlm hM
    rw [← tor_swap] at h2
    exact ⟨M', Or.inr h1, h2⟩

theorem conj_closure {l m : K} (hml : m * σ l = 1) {n : Matrix ι ι K}
    (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ n' ∈ Submonoid.closure (eichSet σ J e f), tor σ J e f l m * n = n' * tor σ J e f l m := by
  induction hn using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨M', h1, h2⟩ := conj_mem_eichSet hσ hJ he hff hef hml hx
    exact ⟨M', Submonoid.subset_closure h1, h2⟩
  | one => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx2⟩ := hx
    obtain ⟨y', hy', hy2⟩ := hy
    refine ⟨x' * y', Submonoid.mul_mem _ hx' hy', ?_⟩
    rw [← Matrix.mul_assoc, hx2, Matrix.mul_assoc, hy2, Matrix.mul_assoc]

theorem tor_mul (l m l' m' : K) :
    tor σ J e f l m * tor σ J e f l' m' = tor σ J e f (l * l') (m * m') := by
  rw [tor_hm, tor_hm, tor_hm, hm_mul hσ hJ he hff hef]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem tor_one : tor σ J e f 1 1 = 1 := by
  simp [tor]

end


variable (σ J) in
def Good (σ : K →+* K) (J : Matrix ι ι K) (e f : ι → K) : Set (Matrix ι ι K) :=
  {g | ∃ n ∈ Submonoid.closure (eichSet σ J e f), ∃ l m : K, m * σ l = 1 ∧ g = n * tor σ J e f l m}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem good_of_closure {n : Matrix ι ι K} (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    n ∈ Good σ J e f :=
  ⟨n, hn, 1, 1, by rw [map_one, one_mul], by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩

theorem good_tor {l m : K} (hml : m * σ l = 1) : tor σ J e f l m ∈ Good σ J e f :=
  ⟨1, Submonoid.one_mem _, l, m, hml, by rw [Matrix.one_mul]⟩

theorem good_mul {g g' : Matrix ι ι K} (hg : g ∈ Good σ J e f) (hg' : g' ∈ Good σ J e f) :
    g * g' ∈ Good σ J e f := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨n', hn', l', m', hml', rfl⟩ := hg'
  obtain ⟨n'', hn'', h⟩ := conj_closure hσ hJ he hff hef hml hn'
  refine ⟨n * n'', Submonoid.mul_mem _ hn hn'', l * l', m * m', ?_, ?_⟩
  · rw [map_mul]; linear_combination (m' * σ l') * hml + hml'
  · rw [← tor_mul hσ hJ he hff hef, Matrix.mul_assoc n, ← Matrix.mul_assoc (tor σ J e f l m), h]
    simp only [Matrix.mul_assoc]

theorem good_inv {g : Matrix ι ι K} (hg : g ∈ Good σ J e f) :
    ∃ g' ∈ Good σ J e f, g' * g = 1 ∧ g * g' = 1 := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨ni, hni, h1, h2⟩ := closure_inv hσ hJ he hff hn
  have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
  have hml' : σ l * σ (σ m) = 1 := by rw [hσ, mul_comm, hml]
  refine ⟨tor σ J e f (σ m) (σ l) * ni, good_mul hσ hJ he hff hef (good_tor hσ hJ he hff hef hml')
    (good_of_closure hσ hJ he hff hef hni), ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ni, h1, Matrix.one_mul, tor_mul hσ hJ he hff hef,
      mul_comm (σ m), hlm, mul_comm (σ l) m, hml, tor_one hσ hJ he hff hef]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (tor σ J e f l m), tor_mul hσ hJ he hff hef, hlm,
      hml, tor_one hσ hJ he hff hef, Matrix.one_mul, h2]

theorem good_SU {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {g : Matrix ι ι K}
    (hg : g ∈ Good σ J e f) (hdet : g.det = 1) : g ∈ Submonoid.closure (eichSet σ J e f) := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  have hn1 : n.det = 1 := (closure_sub hσ hJ he hff hn).1
  rw [det_mul, hn1, one_mul, tor_det hσ hJ he hff hef] at hdet
  have hl : σ l = l := by
    calc σ l = (l * m) * σ l := by rw [hdet, one_mul]
      _ = l * (m * σ l) := by ring
      _ = l := by rw [hml, mul_one]
  obtain ⟨di, hdi⟩ := hδ.exists_right_inv
  exact Submonoid.mul_mem _ hn (tor_mem_closure hσ hJ he hff hef hσδ hdi hl hdet)

end

end ReciprocityTheory.ChartRestriction.G.SA
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.ReachableFixingAddSmulSecond

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}


variable (σ J) in
def Reach (e f : ι → K) {s : ℕ} (a : Fin s → ι → K) (b b' : ι → K) : Prop :=
  ∃ p ∈ Good (σ := σ) (J := J) e f, (∀ j, p *ᵥ a j = a j) ∧ p *ᵥ b = b'

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef

theorem reach_refl (b : ι → K) : Reach σ J e f a b b := by
  have h1 : (1 : Matrix ι ι K) ∈ Good (σ := σ) (J := J) e f :=
    ⟨1, Submonoid.one_mem _, 1, 1, by simp, by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩
  exact ⟨1, h1, fun j => Matrix.one_mulVec _, Matrix.one_mulVec _⟩

theorem reach_trans {b b' b'' : ι → K} (h1 : Reach σ J e f a b b') (h2 : Reach σ J e f a b' b'') :
    Reach σ J e f a b b'' := by
  obtain ⟨p1, hp1, ha1, hb1⟩ := h1
  obtain ⟨p2, hp2, ha2, hb2⟩ := h2
  have hp : p2 * p1 ∈ Good (σ := σ) (J := J) e f := by
    obtain ⟨n1, hn1, l1, m1, hml1, rfl⟩ := hp1
    obtain ⟨n2, hn2, l2, m2, hml2, rfl⟩ := hp2
    obtain ⟨n', hn', h⟩ := conj_closure hσ hJ he hff hef hml2 hn1
    refine ⟨n2 * n', Submonoid.mul_mem _ hn2 hn', l2 * l1, m2 * m1, ?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hml2, hml1, mul_one]
    · rw [← tor_mul hσ hJ he hff hef, Matrix.mul_assoc n2,
        ← Matrix.mul_assoc (tor σ J e f l2 m2), h]
      simp only [Matrix.mul_assoc]
  refine ⟨p2 * p1, hp, fun j => ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ha1, ha2]
  · rw [← Matrix.mulVec_mulVec, hb1, hb2]

theorem reach_symm {b b' : ι → K} (h : Reach σ J e f a b b') : Reach σ J e f a b' b := by
  obtain ⟨p, hp, ha, hb⟩ := h
  obtain ⟨g', hg', hg'p⟩ : ∃ g' ∈ Good (σ := σ) (J := J) e f, g' * p = 1 := by
    obtain ⟨n, hn, l, m, hml, rfl⟩ := hp
    obtain ⟨ni, hni, hnin, -⟩ := closure_inv hσ hJ he hff hn
    have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
    have hml' : σ l * σ (σ m) = 1 := by rw [hσ, mul_comm, hml]
    obtain ⟨n', hn', hconj⟩ := conj_closure hσ hJ he hff hef hml' hni
    refine ⟨tor σ J e f (σ m) (σ l) * ni, ⟨n', hn', σ m, σ l, hml', hconj⟩, ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ni, hnin, Matrix.one_mul,
      tor_mul hσ hJ he hff hef, mul_comm (σ m), hlm, mul_comm (σ l) m, hml,
      tor_one hσ hJ he hff hef]
  refine ⟨g', hg', fun j => ?_, ?_⟩
  · conv_lhs => rw [← ha j]
    rw [Matrix.mulVec_mulVec, hg'p, Matrix.one_mulVec]
  · rw [← hb, Matrix.mulVec_mulVec, hg'p, Matrix.one_mulVec]

include hae haf

theorem reach_eich_e {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J e u c *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have hn : eich σ J e u c ∈ Submonoid.closure (eichSet σ J e f) :=
    Submonoid.subset_closure (Or.inl ⟨u, c, hue, huf, hc, rfl⟩)
  refine ⟨eich σ J e u c,
    ⟨_, hn, 1, 1, by simp, by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩, fun j => ?_, rfl⟩
  rw [hE, hae j, ← hf_symm hσ hJ u (a j), hua j, map_zero]
  simp

theorem reach_eich_f {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J f u c *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have hn : eich σ J f u c ∈ Submonoid.closure (eichSet σ J e f) :=
    Submonoid.subset_closure (Or.inr ⟨u, c, huf, hue, hc, rfl⟩)
  refine ⟨eich σ J f u c,
    ⟨_, hn, 1, 1, by simp, by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩, fun j => ?_, rfl⟩
  rw [hE, haf j, ← hf_symm hσ hJ u (a j), hua j, map_zero]
  simp

theorem reach_tor {l m : K} (hml : m * σ l = 1) (b : ι → K) :
    Reach σ J e f a b (tor σ J e f l m *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨tor σ J e f l m, ⟨1, Submonoid.one_mem _, l, m, hml, by rw [Matrix.one_mul]⟩,
    fun j => ?_, rfl⟩
  simp only [tor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hvmv, hdot,
    haf j, hae j, zero_smul, smul_zero, add_zero]

theorem reachableFixing_add_smul_first {c : K} (hc : σ c = -c) (b : ι → K) :
    Reach σ J e f a b (b + (c * hf σ J b e) • e) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have h0 : ∀ v : ι → K, hf σ J 0 v = 0 := fun v => by simp [hf]
  have h0' : ∀ v : ι → K, hf σ J v 0 = 0 := fun v => by simp [hf]
  have := reach_eich_e hσ hJ he hff hef hae haf (u := 0) (c := c) (h0 e) (h0 f)
    (by rw [hc, h0]; ring) (fun j => h0 _) b
  convert this using 1
  rw [hE, h0']
  simp

theorem reachableFixing_add_smul_second {c : K} (hc : σ c = -c) (b : ι → K) :
    Reach σ J e f a b (b + (c * hf σ J b f) • f) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have h0 : ∀ v : ι → K, hf σ J 0 v = 0 := fun v => by simp [hf]
  have h0' : ∀ v : ι → K, hf σ J v 0 = 0 := fun v => by simp [hf]
  have := reach_eich_f hσ hJ he hff hef hae haf (u := 0) (c := c) (h0 e) (h0 f)
    (by rw [hc, h0]; ring) (fun j => h0 _) b
  convert this using 1
  rw [hE, h0']
  simp

theorem good_preserves {p : Matrix ι ι K} (hp : p ∈ Good (σ := σ) (J := J) e f) (x y : ι → K) :
    hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hp
  have key : ∀ g ∈ Submonoid.closure (eichSet σ J e f), ∀ x y : ι → K,
      hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      intro x y
      rcases hg with ⟨u, c, hue, huf, hc, rfl⟩ | ⟨u, c, huf, hue, hc, rfl⟩
      · apply eich_preserves <;> assumption
      · apply eich_preserves <;> assumption
    | one => intro x y; simp
    | mul g h _ _ ihg ihh =>
      intro x y
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ihg, ihh]
  have ht : ∀ x y : ι → K, hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by
    intro x y
    apply tor_preserves <;> assumption
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key n hn, ht]

theorem reach_inv {b b' : ι → K} (h : Reach σ J e f a b b') (hb : ∀ j, hf σ J b (a j) = 0) :
    (∀ j, hf σ J b' (a j) = 0) ∧ hf σ J b' b' = hf σ J b b := by
  obtain ⟨p, hp, ha, rfl⟩ := h
  refine ⟨fun j => ?_, good_preserves hσ hJ he hff hef hae haf hp b b⟩
  rw [← ha j, good_preserves hσ hJ he hff hef hae haf hp, hb]

end

end ReciprocityTheory.ChartRestriction.G.SA
end
end
