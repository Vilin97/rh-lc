module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.StatementO
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.PresIso
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Nakayama
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.QuadRoots

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.QuadBasis

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

section
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]

theorem qb_unit_of_not_dvd {p : ℕ} (hpW : Irreducible (p : W)) {b : W} (hb : ¬ (p : W) ∣ b) :
    IsUnit b := by
  by_contra h
  have h1 : b ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal b).2 h
  rw [hpW.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
  exact hb h1

theorem qb_I {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b : W} (h : w ∣ j a + j b * θ) :
    (p : W) ∣ a ∧ (p : W) ∣ b := by
  have hb : (p : W) ∣ b := by
    by_contra hb
    obtain ⟨u, rfl⟩ := qb_unit_of_not_dvd hpW hb
    apply hθ (-(↑u⁻¹ * a))
    have h0 := Dvd.dvd.mul_left h (j ↑u⁻¹)
    have e : j ↑u⁻¹ * (j a + j ↑u * θ) = θ - j (-(↑u⁻¹ * a)) := by
      have h1 : j ↑u⁻¹ * j ↑u = 1 := by rw [← map_mul]; simp
      rw [map_neg, map_mul]
      linear_combination θ * h1
    rwa [e] at h0
  refine ⟨?_, hb⟩
  by_contra ha
  have hu := (qb_unit_of_not_dvd hpW ha).map j
  obtain ⟨b', rfl⟩ := hb
  have h2 : w ∣ j ((p : W) * b') * θ := by
    rw [map_mul, map_natCast, ← hw2]
    exact ⟨w * j b' * θ, by ring⟩
  have h3 : w ∣ j a := (dvd_add_left h2).1 h
  exact hw.not_isUnit (isUnit_of_dvd_unit h3 hu)

theorem qb_S {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hw2 : w ^ 2 = (p : O)) (hw : Irreducible w)
    (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n')) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ (a b : W) (x' : O), x = j a + j b * θ + w * x' := by
  have hle : Ideal.span {(p : W)} ≤ Ideal.comap j (Ideal.span {w}) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hw2, Ideal.mem_span_singleton]
    exact dvd_pow_self w two_ne_zero
  let ι := Ideal.quotientMap (Ideal.span {w}) j hle
  let g : (W ⧸ Ideal.span {(p : W)}) × (W ⧸ Ideal.span {(p : W)}) → O ⧸ Ideal.span {w} :=
    fun t => ι t.1 + ι t.2 * Ideal.Quotient.mk _ θ
  have hg : ∀ a b : W, g (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b)
      = Ideal.Quotient.mk _ (j a + j b * θ) := by
    intro a b
    simp only [g, ι, Ideal.quotientMap_mk, map_add (f := _), map_mul]
  have hinj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hg, hg, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h2 : w ∣ j (a - a') + j (b - b') * θ := by
      have e : j (a - a') + j (b - b') * θ = j a + j b * θ - (j a' + j b' * θ) := by
        simp only [map_sub]; ring
      rwa [e]
    obtain ⟨h3, h4⟩ := qb_I j w θ hpW hw2 hw hθ h2
    have k3 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) a = Ideal.Quotient.mk _ a' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h3)
    have k4 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) b = Ideal.Quotient.mk _ b' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h4)
    rw [k3, k4]
  haveI : Finite (O ⧸ Ideal.span {w}) :=
    Nat.finite_of_card_ne_zero (by rw [cO]; exact (pow_pos hp.pos _).ne')
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, cW, cO, two_mul, pow_add])
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [hg, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hab
  obtain ⟨x', hx'⟩ := hab
  exact ⟨a, b, x', by linear_combination hx'⟩

theorem qb_step {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) :
    ∃ a' b' c' d' : W, a = p * a' ∧ b = p * b' ∧ c = p * c' ∧ d = p * d' ∧
      j a' + j b' * θ + j c' * w + j d' * θ * w = 0 := by
  have hw0 : w ≠ 0 := hw.ne_zero
  have h1 : w ∣ j a + j b * θ := ⟨-(j c + j d * θ), by linear_combination h⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h1
  simp only [map_mul, map_natCast, ← hw2] at h
  have h2 : w * (w * (j a' + j b' * θ) + (j c + j d * θ)) = 0 := by linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_left hw0
  have h4 : w ∣ j c + j d * θ := ⟨-(j a' + j b' * θ), by linear_combination h3⟩
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h4
  simp only [map_mul, map_natCast, ← hw2] at h3
  refine ⟨a', b', c', d', rfl, rfl, rfl, rfl, ?_⟩
  have h5 : w * (j a' + j b' * θ + j c' * w + j d' * θ * w) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h5).resolve_left hw0

theorem qb_pow {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (m : ℕ) : ∀ {a b c d : W},
    j a + j b * θ + j c * w + j d * θ * w = 0 →
    (p : W) ^ m ∣ a ∧ (p : W) ^ m ∣ b ∧ (p : W) ^ m ∣ c ∧ (p : W) ^ m ∣ d := by
  induction m with
  | zero => intro a b c d _; simp
  | succ m ih =>
    intro a b c d h
    obtain ⟨a', b', c', d', rfl, rfl, rfl, rfl, h'⟩ := qb_step j w θ hpW hw2 hw hθ h
    obtain ⟨ha, hb, hc, hd⟩ := ih h'
    simp only [pow_succ']
    exact ⟨mul_dvd_mul_left _ ha, mul_dvd_mul_left _ hb, mul_dvd_mul_left _ hc, mul_dvd_mul_left _ hd⟩

theorem qb_zero_of_pow {p : ℕ} (hpW : Irreducible (p : W)) {a : W} (h : ∀ m, (p : W) ^ m ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpW.not_isUnit ha
  exact hn (h _)

theorem qb_indep {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.2⟩

theorem qb_span {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hfin : j.Finite) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n'))
    (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ a b c d : W, x = j a + j b * θ + j c * w + j d * θ * w := by
  letI : Algebra W O := j.toAlgebra
  haveI : Module.Finite W O := hfin
  have hsm : ∀ (r : W) (y : O), r • y = j r * y := fun r y => Algebra.smul_def r y
  let M : Submodule W O :=
    { carrier := {y | ∃ a b c d : W, y = j a + j b * θ + j c * w + j d * θ * w}
      add_mem' := by
        rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
        exact ⟨a + a', b + b', c + c', d + d', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, 0, 0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨a, b, c, d, rfl⟩
        exact ⟨r * a, r * b, r * c, r * d, by rw [hsm]; simp only [map_mul]; ring⟩ }
  have hJ : Ideal.span {(p : W)} ≤ Ideal.jacobson (⊥ : Ideal W) := by
    rw [← hpW.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  have hle : (⊤ : Submodule W O) ≤ M ⊔ Ideal.span {(p : W)} • (⊤ : Submodule W O) := by
    intro y _
    obtain ⟨a, b, y', hy⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y
    obtain ⟨c, d, y'', hy'⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y'
    refine Submodule.mem_sup.2 ⟨j a + j b * θ + j c * w + j d * θ * w, ⟨a, b, c, d, rfl⟩,
      (p : W) • y'', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top, ?_⟩
    rw [hsm, map_natCast, ← hw2, hy, hy']
    ring
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ hle
  exact htop (Submodule.mem_top : x ∈ ⊤)

end

theorem basisCriterion_holds : QuadBasis := by
  intro p n' hp W O _ _ _ _ _ _ j w θ hpW cW hfin hw2 hw cO hθ x
  obtain ⟨a, b, c, d, hx⟩ := qb_span hp j w θ hpW cW hfin hw2 hw cO hθ x
  refine ⟨(a, b, c, d), hx, ?_⟩
  rintro ⟨a', b', c', d'⟩ hx'
  simp only at hx'
  have h : j (a' - a) + j (b' - b) * θ + j (c' - c) * w + j (d' - d) * θ * w = 0 := by
    simp only [map_sub]
    linear_combination hx - hx'
  obtain ⟨h1, h2, h3, h4⟩ := qb_indep j w θ hpW hw2 hw hθ h
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3, sub_eq_zero.1 h4]

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.OIsoOf

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

theorem oIso_of (hR : QuadRoots)
    (p n' : ℕ) (hp : p.Prime) (hn : 0 < n') (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [IsDomain W₁]
    [IsDiscreteValuationRing W₁] [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [CommRing O₁]
    [IsDomain O₁] [IsDiscreteValuationRing O₁] [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂]
    (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂) (w₁ : O₁) (w₂ : O₂) (a₁ : Irreducible (p : W₁))
    (a₂ : Irreducible (p : W₂)) (b₁ : Nat.card (W₁ ⧸ Ideal.span {(p : W₁)}) = p ^ n')
    (b₂ : Nat.card (W₂ ⧸ Ideal.span {(p : W₂)}) = p ^ n') (c₁ : IsAdicComplete (Ideal.span {(p : W₁)}) W₁)
    (c₂ : IsAdicComplete (Ideal.span {(p : W₂)}) W₂) (d₁ : j₁.Finite) (d₂ : j₂.Finite)
    (e₁ : IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁) (e₂ : IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂)
    (f₁ : w₁ ^ 2 = (p : O₁)) (f₂ : w₂ ^ 2 = (p : O₂)) (g₁ : Irreducible w₁) (g₂ : Irreducible w₂)
    (h₁ : Nat.card (O₁ ⧸ Ideal.span {w₁}) = p ^ (2 * n')) (h₂ : Nat.card (O₂ ⧸ Ideal.span {w₂}) = p ^ (2 * n'))
    (φW : W₁ ≃+* W₂) : ∃ φO : O₁ ≃+* O₂, (∀ x, φO (j₁ x) = j₂ (φW x)) ∧ φO w₁ = w₂ := by
  obtain ⟨f0, f1, θ₁, θ₂, r₁, r₂, s₁, s₂⟩ :=
    hR p n' hp hn W₁ W₂ O₁ O₂ j₁ j₂ w₁ w₂ a₁ a₂ b₁ b₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ φW
  have B₁ := basisCriterion_holds p n' hp W₁ O₁ j₁ w₁ θ₁ a₁ b₁ d₁ f₁ g₁ h₁ s₁
  have B₂ := basisCriterion_holds p n' hp W₂ O₂ j₂ w₂ θ₂ a₂ b₂ d₂ f₂ g₂ h₂ s₂
  obtain ⟨φO, k1, k2, _⟩ := presentationIso_holds W₁ W₂ O₁ O₂ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 (p : W₁) φW r₁ r₂
    (by rw [f₁, map_natCast]) (by rw [f₂, map_natCast, map_natCast]) B₁ B₂
  exact ⟨φO, k1, k2⟩

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.FinalO

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

theorem oIso (p n' : ℕ) (hp : p.Prime) (hn : 0 < n') (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂] (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂) (w₁ : O₁) (w₂ : O₂)
 (a₁ : Irreducible (p : W₁)) (a₂ : Irreducible (p : W₂)) (b₁ : Nat.card (W₁ ⧸ Ideal.span {(p : W₁)}) = p ^ n') (b₂ : Nat.card (W₂ ⧸ Ideal.span {(p : W₂)}) = p ^ n') (c₁ : IsAdicComplete (Ideal.span {(p : W₁)}) W₁) (c₂ : IsAdicComplete (Ideal.span {(p : W₂)}) W₂) (d₁ : j₁.Finite) (d₂ : j₂.Finite) (e₁ : IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁) (e₂ : IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂) (f₁ : w₁ ^ 2 = (p : O₁)) (f₂ : w₂ ^ 2 = (p : O₂)) (g₁ : Irreducible w₁) (g₂ : Irreducible w₂) (h₁ : Nat.card (O₁ ⧸ Ideal.span {w₁}) = p ^ (2 * n')) (h₂ : Nat.card (O₂ ⧸ Ideal.span {w₂}) = p ^ (2 * n')) (φW : W₁ ≃+* W₂) : ∃ φO : O₁ ≃+* O₂, (∀ x, φO (j₁ x) = j₂ (φW x)) ∧ φO w₁ = w₂ :=
  oIso_of existsCompatibleRoots_holds p n' hp hn W₁ W₂ O₁ O₂ j₁ j₂ w₁ w₂ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ φW

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem restOIso : RestOIso := fun p n' R₁ R₂ φW =>
  QuadraticBasis.oIso p n' R₁.std.1.prime (by have := R₁.std.1.two_le; omega) R₁.W R₂.W R₁.O R₂.O R₁.jO R₂.jO R₁.w R₂.w
    R₁.std.1.p_unif R₂.std.1.p_unif R₁.std.1.res_card R₂.std.1.res_card R₁.std.1.eq_sum_herm_smul_frame_of_inW R₂.std.1.eq_sum_herm_smul_frame_of_inW
    R₁.std.1.finite R₂.std.1.finite R₁.std.1.complete_O R₂.std.1.complete_O R₁.std.1.w_sq R₂.std.1.w_sq
    R₁.std.2.1 R₂.std.2.1 R₁.std.2.2.1 R₂.std.2.2.1 φW

end Formalism.MainNotions.flipOneThree.Pf
end
end
