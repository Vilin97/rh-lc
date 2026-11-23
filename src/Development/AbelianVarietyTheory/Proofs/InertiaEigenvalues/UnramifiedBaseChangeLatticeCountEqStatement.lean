module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianDualInvAlgBaseChangeUnramifiedIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeOverUnramifiedExtIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralUnramifiedExtIffIsIntegralBase

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem isIntegral_overExt_iff (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (a : B.A) : @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  classical
  choose ι hι using fun c => exists_int_image hU c
  have inj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  let f : K.O →+* K'.O :=
    { toFun := ι
      map_one' := inj (by rw [hι]; simp)
      map_mul' := fun x y => inj (by simp [hι])
      map_zero' := inj (by rw [hι]; simp)
      map_add' := fun x y => inj (by simp [hι]) }
  have hf : ∀ c, algebraMap K'.O K'.E (f c) = φ (algebraMap K.O K.E c) := hι
  letI : Algebra K.O K'.O := f.toAlgebra
  letI iC : Algebra K'.O B.A := (overExt φ B ψ hψ hσ).aO
  have hC : ∀ y : K'.O, algebraMap K'.O B.A y = ψ (algebraMap K'.O K'.E y) := fun _ => rfl
  haveI : IsScalarTower K.O K'.O B.A := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A c, RingHom.algebraMap_toAlgebra, hC]
    show _ = ψ (algebraMap K'.O K'.E (f c))
    rw [hf, hψ]
  show IsIntegral K'.O a ↔ IsIntegral K.O a
  constructor
  · intro h
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
    haveI : Module.Finite K.O K'.O := by
      refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
      obtain ⟨c, hc⟩ := hu y
      have hy : y = ∑ i, c i • u i := by
        apply inj

        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
      rw [hy]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp
    haveI : Algebra.IsIntegral K.O K'.O := Algebra.IsIntegral.of_finite K.O K'.O
    exact isIntegral_trans (R := K.O) (A := K'.O) a h
  · intro h
    exact h.tower_top

end GlobalTheory.UnitLemma.Unr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralUnramifiedExtIffIsIntegralBaseStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  first | exact @GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedOrbitSumCongrCoefficientRing

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma

theorem coe_mulLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) (t : Aˣ) :
    (mulLat O' (t : A) L' : Set A) = mulLat O (t : A) L := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_mulLat, mem_mulLat, ← SetLike.mem_coe, h, SetLike.mem_coe]

theorem stabLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) :
    stabLat O' L' = stabLat O L := by
  ext t
  change (∀ y, y ∈ L' ↔ (t : A) * y ∈ L') ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L
  simp only [← SetLike.mem_coe, h]

theorem orbSum_congr_coe {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A]
    (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A))
    (hX : ∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) (hX' : ∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L')
    (hG : intUnits O A ⊓ G = intUnits O' A ⊓ G) :
    orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  classical
  rw [orbSum_eq, orbSum_eq]
  let f : X → X' := fun L => ⟨Classical.choose (hX L.1 L.2), (Classical.choose_spec (hX L.1 L.2)).1⟩
  have hf : ∀ L : X, ((f L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX L.1 L.2)).2
  let g : X' → X := fun L => ⟨Classical.choose (hX' L.1 L.2), (Classical.choose_spec (hX' L.1 L.2)).1⟩
  have hg : ∀ L : X', ((g L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX' L.1 L.2)).2
  let e : X ≃ X' :=
    { toFun := f
      invFun := g
      left_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hg, hf]))
      right_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hf, hg])) }
  let q : Orb O G X ≃ Orb O' G X' := Quot.congr e (by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      change ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A)
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t, h]
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      have h' : ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A) := congrArg SetLike.coe h
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t] at h'
      exact h')
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun o => ?_
  induction o using Quot.ind with
  | mk L =>
    change (((stabLat O' (f L).1 ⊓ G).relIndex (intUnits O' A ⊓ G) : ℕ) : ℚ) =
      (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
    rw [stabLat_of_coe_eq L.1 (f L).1 (hf L), hG]

end GlobalTheory.UnitLemma.Orbit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedOrbitSumCongrCoefficientRingStatement

section

@[expose] public section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.weightedOrbitSum_congr_coefficientRing : ∀ {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A] (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A)), (∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) → (∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L') → intUnits O A ⊓ G = intUnits O' A ⊓ G → orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  first | exact @GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | exact GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | (intros; apply GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedBaseChangeLatticeCountEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem N_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  intro K K' d φ hU B ψ hψ hσ hO x
  refine (@GlobalTheory.T.weightedOrbitSum_congr_coefficientRing K.O K'.O B.A _ _ B.cA B.aO (overExt φ B ψ hψ hσ).aO B.T (B.X x) ((overExt φ B ψ hψ hσ).X x) ?_ ?_ ?_)
  · intro L hL
    let S : Subalgebra K.O B.A :=
      { carrier := {a | ∀ z ∈ L, a * z ∈ L}
        mul_mem' := fun {a b} ha hb z hz => by rw [mul_assoc]; exact ha _ (hb z hz)
        add_mem' := fun {a b} ha hb z hz => by rw [add_mul]; exact L.add_mem (ha z hz) (hb z hz)
        algebraMap_mem' := fun c z hz => by rw [← Algebra.smul_def]; exact L.smul_mem c hz }
    have hS : Algebra.adjoin K.O ({B.g} : Set B.A) ≤ S := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact fun z hz => hL.2.1 z hz
    let L' : Submodule K'.O (overExt φ B ψ hψ hσ).A :=
      { carrier := (L : Set B.A)
        add_mem' := fun ha hb => L.add_mem ha hb
        zero_mem' := L.zero_mem
        smul_mem' := fun c z hz => hS (hO c) z hz }
    refine ⟨L', ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' L rfl).2 hL.1, fun y hy => hL.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y).symm
  · intro L' hL'
    let M : Submodule K.O B.A :=
      { carrier := (L' : Set B.A)
        add_mem' := fun ha hb => L'.add_mem ha hb
        zero_mem' := L'.zero_mem
        smul_mem' := fun c z hz => by
          obtain ⟨b, hb⟩ := exists_int_image hU c
          have h : c • z = ψ (algebraMap K'.O K'.E b) * z := by
            rw [Algebra.smul_def, hb, hψ, ← IsScalarTower.algebraMap_apply]
          rw [h]; exact L'.smul_mem b hz }
    refine ⟨M, ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' M rfl).1 hL'.1, fun y hy => hL'.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL'.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y)
  · ext t
    simp only [Subgroup.mem_inf]
    refine and_congr_left' ?_
    change (IsIntegral K.O (t : B.A) ∧ IsIntegral K.O ((t⁻¹ : B.Aˣ) : B.A)) ↔
      (@IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ (t : B.A) ∧ @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ ((t⁻¹ : B.Aˣ) : B.A))
    rw [GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ, GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ]

end GlobalTheory.UnitLemma.Unr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedBaseChangeLatticeCountEqStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.unramifiedBaseChange_latticeCount_eq : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  first | exact @GlobalTheory.UnitLemma.Unr.N_overExt | exact GlobalTheory.UnitLemma.Unr.N_overExt | (intros; apply GlobalTheory.UnitLemma.Unr.N_overExt <;> assumption)
end
end
