module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPowEq

section

@[expose] public section

open Polynomial IsLocalRing

namespace GlobalTheory.UnitPowerExistence

theorem exists_unit_pow_eq (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hpos : 0 < q)
    (w : Oˣ) : ∃ v : Oˣ, v ^ q = w := by
  have hq0 : (q : ResidueField O) ≠ 0 := by
    have h := hq.map (residue O)
    rw [map_natCast] at h
    exact h.ne_zero
  have hw : residue O (w : O) ≠ 0 := (w.isUnit.map (residue O)).ne_zero
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (X ^ q - C (residue O (w : O)))
    (by rw [degree_X_pow_sub_C hpos]; exact_mod_cast hpos.ne') (separable_X_pow_sub_C _ hq0 hw)
  obtain ⟨b, rfl⟩ := residue_surjective a₀
  have hb : b ^ q - (w : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, map_pow]
    simpa [IsRoot] using ha₀
  have hbu : IsUnit b := by
    by_contra hb'
    have h2 : b ^ q ∈ maximalIdeal O := Ideal.pow_mem_of_mem _ ((mem_maximalIdeal b).2 hb') q hpos
    have h3 : (w : O) ∈ maximalIdeal O := by simpa using sub_mem h2 hb
    exact (mem_maximalIdeal _).1 h3 w.isUnit
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ q - C (w : O)) (monic_X_pow_sub_C _ hpos.ne') b
    (by simpa using hb) (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
      exact hq.mul (hbu.pow (q - 1)))
  have hapow : a ^ q = w := by simpa [IsRoot, sub_eq_zero] using ha
  have hau : IsUnit a := (isUnit_pow_iff hpos.ne').1 (hapow ▸ w.isUnit)
  exact ⟨hau.unit, Units.ext (by simpa using hapow)⟩

end GlobalTheory.UnitPowerExistence
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  first | (exact @GlobalTheory.VertUnits.units_eq_const_mul_unit) | (exact GlobalTheory.VertUnits.units_eq_const_mul_unit) | (intros; apply GlobalTheory.VertUnits.units_eq_const_mul_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationPowSurj

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.LocAcycUnits

open Polynomial

theorem units_pow_surj_of_sepClosed (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hq0 : 0 < q) (w : Oˣ) :
    ∃ v : Oˣ, v ^ q = w := by
  first
  | exact @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | (apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq ..)

theorem units_localization_pow_surj : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ v : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, v ^ q = u := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hO u
  obtain ⟨_, hroot⟩ := hT
  obtain ⟨c, d, w, hc, hd, hu⟩ := GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit T O hroot hO u
  set L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have root : ∀ x : T, x ≠ 0 → ∃ y : T, y ≠ 0 ∧ y ^ q = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hroot (X ^ q - C x) (monic_X_pow_sub_C _ hq0.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hq0)
    have hyq : y ^ q = x := by simpa [sub_eq_zero] using hy
    refine ⟨y, ?_, hyq⟩
    rintro rfl; exact hx (by rw [← hyq, zero_pow hq0.ne'])
  have unitOf : ∀ x : T, x ≠ 0 → IsUnit (algebraMap O L (algebraMap T O x)) := fun x hx =>
    IsLocalization.map_units L (⟨algebraMap T O x,
      Algebra.mem_algebraMapSubmonoid_of_mem (⟨x, mem_nonZeroDivisors_of_ne_zero hx⟩ :
        nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  obtain ⟨c', hc', hcq⟩ := root c hc
  obtain ⟨d', hd', hdq⟩ := root d hd
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  obtain ⟨w', hw'⟩ := units_pow_surj_of_sepClosed O q hqO hq0 w
  have powU : ∀ (x y : T) (hx : x ≠ 0) (hy : y ≠ 0), y ^ q = x →
      (unitOf y hy).unit ^ q = (unitOf x hx).unit := by
    intro x y hx hy hxy
    apply Units.ext
    simp [← map_pow, hxy]
  have hMw : (Units.map (algebraMap O L).toMonoidHom w') ^ q = Units.map (algebraMap O L).toMonoidHom w := by
    rw [← map_pow, hw']
  have huU : u * (unitOf d hd).unit = (unitOf c hc).unit * Units.map (algebraMap O L).toMonoidHom w := by
    apply Units.ext; simpa using hu
  refine ⟨(unitOf c' hc').unit * Units.map (algebraMap O L).toMonoidHom w' * (unitOf d' hd').unit⁻¹, ?_⟩
  rw [mul_pow, mul_pow, inv_pow, powU c c' hc hc' hcq, powU d d' hd hd' hdq, hMw, ← huU]
  group

end GlobalTheory.LocAcycUnits
end
end
