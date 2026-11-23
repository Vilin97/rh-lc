module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurableStatement

section

@[expose] public section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.mass_mul_volume_commensurable : ∀ {G : Type} [Group G] (Γ' T C C' : Subgroup G), C ≤ T → C' ≤ T → C.relIndex C' ≠ 0 → C'.relIndex C ≠ 0 → (∀ t ∈ T, ((Γ' ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → (∀ t ∈ T, ((Γ' ⊓ C'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → massC Γ' T C' * vol C C' = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.MassChange.massC_mul_vol | exact GlobalTheory.LKCount.MassChange.massC_mul_vol | (intros; apply GlobalTheory.LKCount.MassChange.massC_mul_vol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConj

section

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section ConjInvariance

variable {H : Type} [Group H]

theorem mem_map_conj_iff (B : Subgroup H) (x y : H) :
    y ∈ B.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ B := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨x⁻¹ * y * x, hy, by simp [mul_assoc]⟩

theorem map_conj_mul (B : Subgroup H) (x s : H) :
    (B.map (MulAut.conj s).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      B.map (MulAut.conj (x * s)).toMonoidHom := by
  ext y
  simp only [mem_map_conj_iff, mul_inv_rev]
  simp [mul_assoc]

def stabInv (A B : Subgroup H) (x : H) : ℚ :=
  ((Nat.card (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H) : ℕ) : ℚ)⁻¹

theorem stabInv_mul (A B : Subgroup H) (x : H) {a b : H} (ha : a ∈ A) (hb : b ∈ B) :
    stabInv A B (a * x * b) = stabInv A B x := by
  unfold stabInv
  have e : (A ⊓ B.map (MulAut.conj (a * x * b)).toMonoidHom : Subgroup H) =
      (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H).map (MulAut.conj a).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_inf, mem_map_conj_iff]
    constructor
    · rintro ⟨hyA, hyB⟩
      refine ⟨A.mul_mem (A.mul_mem (A.inv_mem ha) hyA) ha, ?_⟩
      have := B.mul_mem (B.mul_mem hb hyB) (B.inv_mem hb)
      convert this using 1
      group
    · rintro ⟨hzA, hzB⟩
      refine ⟨?_, ?_⟩
      · have := A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha)
        convert this using 1
        group
      · have := B.mul_mem (B.mul_mem (B.inv_mem hb) hzB) hb
        convert this using 1
        group
  rw [e, Nat.card_congr ((A ⊓ B.map (MulAut.conj x).toMonoidHom).equivMapOfInjective _
    (MulAut.conj a).injective).toEquiv.symm]

theorem stabInv_eq_of_mk_eq (A B : Subgroup H) {x y : H}
    (h : DoubleCoset.mk A B x = DoubleCoset.mk A B y) : stabInv A B x = stabInv A B y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
  exact (stabInv_mul A B x ha hb).symm

def dcMulRight (A B : Subgroup H) (s : H) :
    DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H) ≃
      DoubleCoset.Quotient (A : Set H) (B : Set H) :=
  Quotient.congr (Equiv.mulRight s) (by
    intro x y
    rw [← DoubleCoset.eq'', ← DoubleCoset.eq'', DoubleCoset.eq, DoubleCoset.eq]
    simp only [Equiv.coe_mulRight, mem_map_conj_iff]
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨a, ha, s⁻¹ * k * s, hk, by simp [mul_assoc]⟩
    · rintro ⟨a, ha, k, hk, e⟩
      refine ⟨a, ha, s * k * s⁻¹, by simpa [mul_assoc] using hk, ?_⟩
      have := congrArg (· * s⁻¹) e
      simpa [mul_assoc] using this)

theorem dcMulRight_mk (A B : Subgroup H) (s x : H) :
    dcMulRight A B s (DoubleCoset.mk A (B.map (MulAut.conj s).toMonoidHom) x) =
      DoubleCoset.mk A B (x * s) := rfl

theorem finsum_stabInv_conj (A B : Subgroup H) (s : H) :
    (∑ᶠ q : DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H),
      stabInv A (B.map (MulAut.conj s).toMonoidHom) (Quotient.out q)) =
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (B : Set H), stabInv A B (Quotient.out q) := by
  rw [← finsum_comp_equiv (dcMulRight A B s)]
  refine finsum_congr fun q => ?_
  unfold stabInv
  rw [map_conj_mul]
  refine stabInv_eq_of_mk_eq A B ?_
  rw [← dcMulRight_mk, DoubleCoset.out_eq', DoubleCoset.out_eq']

end ConjInvariance

theorem massC_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T →
    massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  intro G _ Γ' T C t ht _
  have hsub : (C.map (MulAut.conj t).toMonoidHom).subgroupOf T =
      (C.subgroupOf T).map (MulAut.conj (⟨t, ht⟩ : T)).toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_map_conj_iff, mem_map_conj_iff, Subgroup.mem_subgroupOf]
    simp
  unfold massC
  rw [hsub]
  exact finsum_stabInv_conj _ _ _

end GlobalTheory.LKCount
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConjStatement

section

@[expose] public section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.twistedCentralizerMass_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T → massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.massC_map_conj | exact GlobalTheory.LKCount.massC_map_conj | (intros; apply GlobalTheory.LKCount.massC_map_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolConjEqOneOfMassCNeZero

section

@[expose] public section

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
end
end
