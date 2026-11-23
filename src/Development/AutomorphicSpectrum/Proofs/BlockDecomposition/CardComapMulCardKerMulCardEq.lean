module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
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
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Isomorphisms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardEqCardKerMulCardRange
public import Mathlib.Data.ZMod.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelf
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorIntersectionCard

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.PairCount

theorem card_comap_subtype {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sup_mul_card_inf {R X : Type} [Ring R] [AddCommGroup X] [Module R X] [Finite X]
    (I L : Submodule R X) :
    Nat.card ↥(I ⊔ L) * Nat.card ↥(I ⊓ L) = Nat.card ↥I * Nat.card ↥L := by
  have e := Nat.card_congr (LinearMap.quotientInfEquivSupQuotient I L).toEquiv
  have hq : I.comap I.subtype ⊓ L.comap I.subtype = L.comap I.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  rw [hq] at e
  have h1 := Submodule.card_eq_card_quotient_mul_card (L.comap I.subtype)
  have h2 := Submodule.card_eq_card_quotient_mul_card (L.comap (I ⊔ L).subtype)
  rw [card_comap_subtype] at h1 h2
  rw [inf_eq_right.2 (le_sup_right : L ≤ I ⊔ L)] at h2
  rw [h1, h2, e]
  ring

theorem bijective_of_injective (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) : Function.Bijective B := by
  have : Finite (X →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have hd : Nat.card (X →ₗ[ZMod n] ZMod n) = Nat.card X := GlobalTheory.ZModDual.card_dual_eq n X
  have hd' : Nat.card (Y →ₗ[ZMod n] ZMod n) = Nat.card Y := GlobalTheory.ZModDual.card_dual_eq n Y
  have : Finite (Y →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have h1 : Nat.card X ≤ Nat.card Y := hd' ▸ Nat.card_le_card_of_injective _ hB'
  exact hB.bijective_of_nat_card_le (hd ▸ h1)

theorem card_annihilator_mul_card (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) * Nat.card ↥U = Nat.card X := by
  let e : Y ≃ (X →ₗ[ZMod n] ZMod n) :=
    Equiv.ofBijective B (bijective_of_injective n X Y B hB hB')
  have h1 : Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) = Nat.card ↥U.dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_dualAnnihilator]
    rfl
  have : Finite (X ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  have h2 : Nat.card ↥U.dualAnnihilator = Nat.card (X ⧸ U) := by
    rw [← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]
    exact GlobalTheory.ZModDual.card_dual_eq n (X ⧸ U)
  rw [h1, h2]
  rw [mul_comm]
  exact (Submodule.card_eq_card_quotient_mul_card U).symm

theorem annihilator_inf (n : ℕ) (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [AddCommGroup Y] [Module (ZMod n) Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n)
    (I L : Submodule (ZMod n) X) :
    (⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x)) =
      ⨅ x ∈ I ⊔ L, LinearMap.ker (B.flip x) := by
  ext y
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩
  obtain ⟨i, hi, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), h.1 i hi, h.2 l hl, add_zero]

theorem card_annihilator_inf (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (I L : Submodule (ZMod n) X) :
    Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) *
        Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  rw [annihilator_inf, mul_assoc, ← card_sup_mul_card_inf, ← mul_assoc,
    card_annihilator_mul_card n X Y B hB hB']

end GlobalTheory.CompanionTheory.PairCount
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorIntersectionCardStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.annihilator_intersection_card : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ I L : Submodule (ZMod n) X, Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) * Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  first | exact @GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | exact GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | (intros; apply GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardComapEqCardKerMulCardRangeInf

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_eq_card_ker_mul_card_range_inf :
    ∀ (R A X : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A] [AddCommGroup X]
      [Module R X] (f : A →ₗ[R] X) (U : Submodule R X),
      Nat.card ↥(U.comap f) = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f ⊓ U) := by
  intro R A X _ _ _ _ _ _ f U
  have hker : LinearMap.ker (f.domRestrict (U.comap f)) ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1.1, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩
      invFun := fun y => ⟨⟨y.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.mp y.2]
          exact U.zero_mem⟩, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hrange : LinearMap.range (f.domRestrict (U.comap f)) = LinearMap.range f ⊓ U := by
    rw [LinearMap.range_domRestrict, Submodule.map_comap_eq]
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (f.domRestrict (U.comap f))),
    Nat.card_congr hker, Nat.card_congr (f.domRestrict (U.comap f)).quotKerEquivRange.toEquiv,
    hrange]

end GlobalTheory.CompanionTheory.Counting
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelfStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.double_annihilator_eq_self : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ U : Submodule (ZMod n) X, (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  first | exact @GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | exact GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | (intros; apply GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardComapMulCardKerMulCardEq

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_mul_card_ker_mul_card_eq :
    ∀ (n : ℕ) [NeZero n] (H H' P P' : Type) [AddCommGroup H] [Module (ZMod n) H] [Finite H] [AddCommGroup H'] [Module (ZMod n) H'] [Finite H'] [AddCommGroup P] [Module (ZMod n) P] [Finite P] [AddCommGroup P'] [Module (ZMod n) P'] [Finite P'] (B : P' →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ (loc : H →ₗ[ZMod n] P) (loc' : H' →ₗ[ZMod n] P'), LinearMap.range loc = (⨅ y ∈ LinearMap.range loc', LinearMap.ker (B y)) → ∀ L : Submodule (ZMod n) P, Nat.card ↥(L.comap loc) * Nat.card ↥(LinearMap.ker loc') * Nat.card P = Nat.card ↥((⨅ x ∈ L, LinearMap.ker (B.flip x)).comap loc') * Nat.card H * Nat.card ↥L := by
  intro n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L
  have e1 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L
  have e2 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc'
    (⨅ x ∈ L, LinearMap.ker (B.flip x))
  have e3 := card_eq_card_ker_mul_card_range (ZMod n) H P loc
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have hdd := GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')
  rw [hflip, ← hR] at hdd
  have e4 := GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L
  rw [hdd] at e4
  rw [e1, e2, e3]
  have key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) =
      Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) *
        Nat.card ↥(LinearMap.range loc) * Nat.card ↥L) := by
    rw [e4]
  linarith [key]

end GlobalTheory.CompanionTheory.Counting
end
end
