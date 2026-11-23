module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.ReachableFixingAddSmulSecond
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.ExistsMaxOfNotCoprime

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.SA

section
variable {K : Type*} [CommRing K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
include hσ hfix

theorem norm_zero_of_not_unit {z : K} (hz : ¬ IsUnit z) : z * σ z = 0 := by
  by_contra h
  have hfx : σ (z * σ z) = z * σ z := by rw [map_mul, hσ, mul_comm]
  exact hz (isUnit_of_mul_isUnit_left (hfix _ hfx h))

theorem gp [IsReduced K] (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {x y : K}
    (hxy : IsCoprime x y) :
    IsUnit x ∨ IsUnit (x + δ * y) ∨ IsUnit (x + (-1) * δ * y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2', h3⟩ := hcon
  have e1 := norm_zero_of_not_unit hσ hfix h1
  have e2 := norm_zero_of_not_unit hσ hfix h2'
  have e3 := norm_zero_of_not_unit hσ hfix h3
  simp only [map_add (f := _), map_mul, hσδ, map_neg, map_one] at e2 e3
  obtain ⟨a, b, hab⟩ := hxy
  have hab' : σ a * σ x + σ b * σ y = 1 := by
    have := congrArg σ hab
    simpa only [map_add (f := _), map_mul, map_one] using this
  have hyy0 : (2 * δ ^ 2) * (y * σ y) = 0 := by linear_combination 2 * e1 - e2 - e3
  have hyy : y * σ y = 0 := ((h2.mul (hδ.pow 2)).mul_right_eq_zero).mp hyy0
  have hxy0 : (2 * δ) * (y * σ x - x * σ y) = 0 := by linear_combination e2 - e3
  have hxy' : y * σ x - x * σ y = 0 := ((h2.mul hδ).mul_right_eq_zero).mp hxy0
  have key : (a * σ b + b * σ a) * (x * σ y) = 1 := by
    linear_combination (σ a * σ x + σ b * σ y) * hab + hab' - σ a * b * hxy' - a * σ a * e1 -
      b * σ b * hyy
  have hu : IsUnit (x * σ y) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact key⟩
  have hsq : (x * σ y) * (x * σ y) = 0 := by
    linear_combination (y * σ y) * e1 - (x * σ y) * hxy'
  have h0 : IsUnit (0 : K) := by
    have := hu.mul hu
    rwa [hsq] at this
  haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
  exact h1 (isUnit_of_subsingleton x)

end

theorem exists_max_of_not_coprime {K : Type*} [CommRing K] {a b : K} (h : ¬ IsCoprime a b) :
    ∃ m : Ideal K, m.IsMaximal ∧ a ∈ m ∧ b ∈ m := by
  have hI : Ideal.span {a, b} ≠ ⊤ := by
    intro hI
    have h1 : (1 : K) ∈ Ideal.span {a, b} := by
      rw [hI]
      exact Submodule.mem_top
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h1
    exact h ⟨c, d, hcd⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  exact ⟨m, hm, hIm (Ideal.subset_span (by simp)), hIm (Ideal.subset_span (by simp))⟩

theorem stepA {K : Type*} [CommRing K] {σ : K →+* K}
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    (h2 : IsUnit (2 : K)) {α β ω ν c : K} (hν : IsUnit ν) (hdef : ν = α * σ β + σ α * β + ω)
    (hnc : ¬ IsCoprime α β) :
    IsCoprime (α - ω + c * β) β ∨ IsCoprime (α + ω + c * β) β := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h1'⟩ := hcon
  obtain ⟨m0, hm0, ha0, hb0⟩ := exists_max_of_not_coprime hnc
  obtain ⟨m1, hm1, ha1, hb1⟩ := exists_max_of_not_coprime h1
  obtain ⟨m2, hm2, ha2, hb2⟩ := exists_max_of_not_coprime h1'
  have key : ∀ m : Ideal K, m.IsMaximal → α ∈ m → β ∈ m → ω ∈ m → False := by
    intro m hm ha hb hw
    have hν' : ν ∈ m := by
      rw [hdef]
      exact m.add_mem (m.add_mem (m.mul_mem_right _ ha) (m.mul_mem_left _ hb)) hw
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hν' hν)
  have hA1 : α - ω ∈ m1 := by
    have := m1.sub_mem ha1 (m1.mul_mem_left c hb1)
    simpa using this
  have hA2 : α + ω ∈ m2 := by
    have := m2.sub_mem ha2 (m2.mul_mem_left c hb2)
    simpa using this
  rcases hmax m0 m1 m2 hm0 hm1 hm2 with h | h | h
  · subst h
    have := m0.sub_mem ha0 hA1
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have := m0.sub_mem hA2 ha0
    exact key m0 hm0 ha0 hb0 (by simpa using this)
  · subst h
    have h2a : 2 * α ∈ m1 := by
      have := m1.add_mem hA1 hA2
      convert this using 1
      ring
    obtain ⟨u, hu⟩ := h2
    have hα : α ∈ m1 := by
      have := m1.mul_mem_left (↑u⁻¹ : K) h2a
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    have := m1.sub_mem hA2 hα
    exact key m1 hm1 hα hb1 (by simpa using this)

end ReciprocityTheory.ChartRestriction.G.SA
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.HfDecompSelf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem hf_ef_left (x y : K) : hf σ J (x • e + y • f) e = y ∧ hf σ J (x • e + y • f) f = x := by
  have hfe := hf_fe hσ hJ he hff hef
  simp [hf_add_left, hf_smul_left, he, hff, hef, hfe]

theorem decomp (b : ι → K) :
    hf σ J (b - hf σ J b f • e - hf σ J b e • f) e = 0 ∧
      hf σ J (b - hf σ J b f • e - hf σ J b e • f) f = 0 := by
  have hfe := hf_fe hσ hJ he hff hef
  simp [hf_sub_left, hf_smul_left, he, hff, hef, hfe]

theorem hf_decomp_self (x y : K) {w : ι → K} (hwe : hf σ J w e = 0) (hwf : hf σ J w f = 0) :
    hf σ J (x • e + y • f + w) (x • e + y • f + w) = x * σ y + σ x * y + hf σ J w w := by
  have hfe := hf_fe hσ hJ he hff hef
  have hew : hf σ J e w = 0 := by rw [← hf_symm hσ hJ, hwe, map_zero]
  have hfw : hf σ J f w = 0 := by rw [← hf_symm hσ hJ, hwf, map_zero]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, he, hff, hef, hfe, hwe, hwf,
    hew, hfw]
  ring

end

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
include hσ hJ he hff hef hae haf hfix h2i hδ hσδ

theorem stage2 {b : ι → K} (hcop : IsCoprime (hf σ J b f) (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ IsUnit (hf σ J b' e) := by
  have hfe := hf_fe hσ hJ he hff hef
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  rcases gp hσ hfix h2 hδ hσδ hcop.symm with h | h | h
  · exact ⟨b, reach_refl hσ hJ he hff hef b, h⟩
  · refine ⟨_, reachableFixing_add_smul_second hσ hJ he hff hef hae haf hσδ b, ?_⟩
    simpa [hf_add_left, hf_smul_left, hfe] using h
  · refine ⟨_, reachableFixing_add_smul_second hσ hJ he hff hef hae haf (c := -1 * δ) (by rw [map_mul, hσδ]; simp) b, ?_⟩
    simpa [hf_add_left, hf_smul_left, hf_neg_left, neg_smul, hfe, mul_assoc] using h

theorem stage4 {b : ι → K} (hform : b = hf σ J b f • e + hf σ J b e • f)
    (hcop : IsCoprime (hf σ J b f) (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧ IsUnit (hf σ J b' f) := by
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  set α := hf σ J b f
  set β := hf σ J b e
  have hval := fun x y => hf_ef_left hσ hJ he hff hef (e := e) (f := f) x y
  rcases gp hσ hfix h2 hδ hσδ hcop with h | h | h
  · exact ⟨b, reach_refl hσ hJ he hff hef b, hform, h⟩
  · have hb' : b + (δ * β) • e = (α + δ * β) • e + β • f := by rw [hform]; module
    refine ⟨_, reachableFixing_add_smul_first hσ hJ he hff hef hae haf hσδ b, ?_, ?_⟩
    · rw [hb', (hval _ _).1, (hval _ _).2]
    · rw [hb', (hval _ _).2]; exact h
  · have hb' : b + (-1 * δ * β) • e = (α + -1 * δ * β) • e + β • f := by rw [hform]; module
    refine ⟨_, reachableFixing_add_smul_first hσ hJ he hff hef hae haf (c := -1 * δ) (by rw [map_mul, hσδ]; simp) b, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc (-1) δ] at hb' ⊢
      rw [hb', (hval _ _).1, (hval _ _).2]
    · rw [mul_assoc, ← mul_assoc (-1) δ] at hb' ⊢
      rw [hb', (hval _ _).2]; exact h

theorem apply_half : σ i2 = i2 := by
  have h1 : 2 * σ i2 = 1 := by
    have := congrArg σ h2i
    rwa [map_mul, map_ofNat, map_one] at this
  linear_combination i2 * h1 - σ i2 * h2i

theorem stage5 {b : ι → K} (hform : b = hf σ J b f • e + hf σ J b e • f) (hα : IsUnit (hf σ J b f)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by
  have hfe := hf_fe hσ hJ he hff hef
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  set α := hf σ J b f
  set β := hf σ J b e
  set ν := hf σ J b b with hνdef
  have hν : ν = α * σ β + σ α * β := by
    rw [hνdef]
    conv_lhs => rw [hform]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, he, hff, hef, hfe]
    ring
  have hσν : σ ν = ν := hf_symm hσ hJ b b
  obtain ⟨αi, hαi⟩ := hα.exists_right_inv
  have hml : σ α * σ αi = 1 := by rw [← map_mul, hαi, map_one]
  have r1 : Reach σ J e f a b (e + (σ α * β) • f) := by
    have := reach_tor hσ hJ he hff hef hae haf hml b
    have htor : tor σ J e f αi (σ α) *ᵥ b = e + (σ α * β) • f := by
      rw [tor_mulVec]
      conv_lhs => rw [hform]
      simp only [hf_add_left, hf_smul_left, hef, hff, he, hfe, mul_one, mul_zero, add_zero, zero_add]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e i * hαi
    rwa [htor] at this
  have hc : σ (ν * i2 - σ α * β) = -(ν * i2 - σ α * β) := by
    rw [map_sub, map_mul, map_mul, hσν, hi2, hσ]
    linear_combination ν * h2i + hν
  have r2 := reachableFixing_add_smul_second hσ hJ he hff hef hae haf hc (e + (σ α * β) • f)
  have hb1f : hf σ J (e + (σ α * β) • f) f = 1 := by
    simp [hf_add_left, hf_smul_left, hef, hff]
  rw [hb1f] at r2
  have heq : e + (σ α * β) • f + ((ν * i2 - σ α * β) * 1) • f = e + (ν * i2) • f := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq] at r2
  exact reach_trans hσ hJ he hff hef r1 r2

theorem stage3 {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hβ : IsUnit (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧ IsUnit (hf σ J b' e) := by
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  obtain ⟨hwe, hwf⟩ := decomp hσ hJ he hff hef b
  set α := hf σ J b f
  set β := hf σ J b e
  set w := b - α • e - β • f with hw
  have hea : ∀ j, hf σ J e (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, hae, map_zero]
  have hfa : ∀ j, hf σ J f (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, haf, map_zero]
  have hwa : ∀ j, hf σ J w (a j) = 0 := fun j => by
    rw [hw, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hb, hea, hfa]; ring
  obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
  set u := (-βi) • w
  set c := -(hf σ J u u * i2)
  have hc : c + σ c + hf σ J u u = 0 := by
    have : σ (hf σ J u u) = hf σ J u u := hf_symm hσ hJ u u
    simp only [c, map_neg, map_mul, this, hi2]
    linear_combination (-hf σ J u u) * h2i
  have r := reach_eich_e hσ hJ he hff hef hae haf (u := u) (c := c)
    (by simp [u, hf_smul_left, hf_neg_left, hwe]) (by simp [u, hf_smul_left, hf_neg_left, hwf]) hc
    (fun j => by simp [u, hf_smul_left, hf_neg_left, hwa]) b
  have hb' : eich σ J e u c *ᵥ b = (α - hf σ J b u + c * β) • e + β • f := by
    rw [eich_mulVec]
    ext i
    simp only [u, hw, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b i - α * e i - β * f i)) * hβi
  rw [hb'] at r
  have hval := hf_ef_left hσ hJ he hff hef (e := e) (f := f) (α - hf σ J b u + c * β) β
  exact ⟨_, r, by rw [hval.1, hval.2], by rw [hval.1]; exact hβ⟩

theorem stage1 (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hν : IsUnit (hf σ J b b)) :
    ∃ b', Reach σ J e f a b b' ∧ IsCoprime (hf σ J b' f) (hf σ J b' e) := by
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  have hfe := hf_fe hσ hJ he hff hef
  by_cases hcop : IsCoprime (hf σ J b f) (hf σ J b e)
  · exact ⟨b, reach_refl hσ hJ he hff hef b, hcop⟩
  obtain ⟨hwe, hwf⟩ := decomp hσ hJ he hff hef b
  set α := hf σ J b f
  set β := hf σ J b e
  set w := b - α • e - β • f with hw
  have hew : hf σ J e w = 0 := by rw [← hf_symm hσ hJ, hwe, map_zero]
  have hfw : hf σ J f w = 0 := by rw [← hf_symm hσ hJ, hwf, map_zero]
  have hea : ∀ j, hf σ J e (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, hae, map_zero]
  have hfa : ∀ j, hf σ J f (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, haf, map_zero]
  have hwa : ∀ j, hf σ J w (a j) = 0 := fun j => by
    rw [hw, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hb, hea, hfa]; ring
  have hbw : b = α • e + β • f + w := by rw [hw]; abel
  obtain ⟨ω, hω⟩ : ∃ ω, ω = hf σ J w w := ⟨_, rfl⟩
  have hdef : hf σ J b b = α * σ β + σ α * β + ω := by
    rw [hω]
    conv_lhs => rw [hbw]
    exact hf_decomp_self hσ hJ he hff hef α β hwe hwf
  have hbwv : hf σ J b w = ω := by
    have h1 : hf σ J b w = α * hf σ J e w + β * hf σ J f w + hf σ J w w := by
      conv_lhs => rw [hbw]
      simp only [hf_add_left, hf_smul_left]
    rw [h1, hew, hfw, hω]; ring
  set c := -(ω * i2)
  have hσω : σ ω = ω := by rw [hω]; exact hf_symm hσ hJ w w
  have smove : ∀ sg : K, σ sg = sg → sg * sg = 1 →
      Reach σ J e f a b (eich σ J e (sg • w) c *ᵥ b) ∧
        hf σ J (eich σ J e (sg • w) c *ᵥ b) f = α - sg * ω + c * β ∧
        hf σ J (eich σ J e (sg • w) c *ᵥ b) e = β := by
    intro sg hs1 hs2
    refine ⟨reach_eich_e hσ hJ he hff hef hae haf (by simp [hf_smul_left, hwe])
      (by simp [hf_smul_left, hwf]) ?_ (fun j => by simp [hf_smul_left, hwa]) b, ?_, ?_⟩
    · simp only [c, hf_smul_left, hf_smul_right, hs1, map_neg, map_mul, hσω, hi2, ← hω]
      linear_combination (-ω) * h2i + ω * hs2
    · rw [eich_mulVec]
      simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hwf, hef, hbwv, hs1]
      ring
    · rw [eich_mulVec]
      simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hwe, he]
      ring
  rcases stepA hmax h2 hν hdef hcop (c := c) with h | h
  · obtain ⟨r, h1, h3⟩ := smove 1 (map_one σ) (one_mul 1)
    refine ⟨_, r, ?_⟩
    rw [h1, h3, one_mul]; exact h
  · obtain ⟨r, h1, h3⟩ := smove (-1) (by rw [map_neg, map_one]) (by ring)
    refine ⟨_, r, ?_⟩
    rw [h1, h3, show α - -1 * ω + c * β = α + ω + c * β by ring]; exact h

end

end ReciprocityTheory.ChartRestriction.G.SA
end
end
