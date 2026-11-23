module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Lemmata.GeneralBFactThirdVersion.Imports

section

@[expose] public section

namespace Bl.general_b_fact_third_version

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [@NumberField.{0} E inst] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 :
    @Module.{0, 0} E V
      (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_4 :
    @Module.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_5 :
    @IsScalarTower.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst) E V
      (@Algebra.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) E
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst))
        (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
        (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst))
      (@SMulZeroClass.toSMul.{0, 0} E V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} E V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} E V
            (@Semiring.toMonoid.{0} E
              (@DivisionSemiring.toSemiring.{0} E
                (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} E V
              (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3))))
      (@SMulZeroClass.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
            (@Semiring.toMonoid.{0} (@NumberField.RingOfIntegers.{0} E inst)
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))))]
  (Λ :
    @Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4),
  @Submodule.IsFullLattice.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst)
      (@NumberField.instCommRingRingOfIntegers.{0} E inst) E (@Field.toCommRing.{0} E inst)
      (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst) V inst_2 inst_4 inst_3 inst_5 Λ →
    ∀ (v : V),
      @Exists.{1} Nat fun (m : Nat) ↦
        And (@Ne.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Membership.mem.{0, 0} V
            (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
              V
              (@Submodule.setLike.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))
            Λ
            (@HSMul.hSMul.{0, 0, 0} E V V
              (@instHSMul.{0, 0} E V
                (@SMulZeroClass.toSMul.{0, 0} E V
                  (@AddZero.toZero.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} E V
                    (@AddMonoid.toAddZeroClass.{0} V
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
                    (@DistribMulAction.toDistribSMul.{0, 0} E V
                      (@Semiring.toMonoid.{0} E
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
                      (@Module.toDistribMulAction.{0, 0} E V
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)))))
              (@Nat.cast.{0} E
                (@AddMonoidWithOne.toNatCast.{0} E
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} E
                    (@Ring.toAddGroupWithOne.{0} E (@DivisionRing.toRing.{0} E (@Field.toDivisionRing.{0} E inst)))))
                m)
              v)) := by
  intro E _ _ V _ _ _ _ Λ hΛ v
  have key : ∀ c : E, ∃ m : ℕ, m ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      (m : E) * c = algebraMap (NumberField.RingOfIntegers E) E a := by
    intro c
    have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (IsAlgebraic.of_finite ℚ c)
    obtain ⟨m, s, hm, h⟩ := hc.exists_nsmul_eq (NumberField.RingOfIntegers E)
    exact ⟨m, hm, s, by rw [← h, nsmul_eq_mul]⟩
  have h1 : ∀ (k : ℕ) (w : V), w ∈ Λ → (k : E) • w ∈ Λ := fun k w hw => by
    rw [Nat.cast_smul_eq_nsmul]; exact Λ.nsmul_mem hw k
  let S : Submodule E V :=
    { carrier := {w | ∃ m : ℕ, m ≠ 0 ∧ (m : E) • w ∈ Λ}
      add_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        rw [Nat.cast_mul, smul_add]
        refine Λ.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact h1 _ _ ha
        · rw [mul_smul]; exact h1 _ _ hb
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨m, hm, hw⟩
        obtain ⟨n, hn, a, ha⟩ := key c
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have e : ((n * m : ℕ) : E) • (c • w) = a • ((m : E) • w) := by
          rw [← algebraMap_smul E a ((m : E) • w), ← ha, Nat.cast_mul, smul_smul, smul_smul]
          congr 1; ring
        rw [e]; exact Λ.smul_mem a hw }
  have hle : Submodule.span E (Λ : Set V) ≤ S :=
    Submodule.span_le.mpr (fun w hw => ⟨1, one_ne_zero, by simpa using hw⟩)
  rw [hΛ.span_eq_top] at hle
  obtain ⟨m, hm, h⟩ := hle (Submodule.mem_top : v ∈ (⊤ : Submodule E V))
  exact ⟨m, hm, h⟩

end Bl.general_b_fact_third_version
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.NatSmulMem

section

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Den

variable {E : Type} [Field E] [NumberField E]

theorem intE_iff (x : E) : IntE x ↔ IsIntegral ℤ x := by
  rw [IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  rfl

theorem intE_zero : IntE (0 : E) := ⟨0, by simp⟩

theorem intE_one : IntE (1 : E) := ⟨1, by simp⟩

theorem intE_nat (k : ℕ) : IntE (k : E) := ⟨k, by simp⟩

theorem intE_add {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by simp⟩

theorem intE_neg {x : E} (hx : IntE x) : IntE (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by simp⟩

theorem intE_mul {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by simp⟩

theorem intE_nat_mul (k : ℕ) {x : E} (hx : IntE x) : IntE ((k : E) * x) := intE_mul (intE_nat k) hx

theorem intE_sum {ι : Type*} (s : Finset ι) (x : ι → E) (h : ∀ i ∈ s, IntE (x i)) : IntE (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intE_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intE_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intE_star [StarRing E] {x : E} (hx : IntE x) : IntE (star x) := by
  rw [intE_iff] at hx ⊢
  exact hx.map (starRingEnd E).toIntAlgHom

theorem den_exists (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IntE ((m : E) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := hx.exists_nsmul_eq (𝓞 E)
  refine ⟨m, hm, s, ?_⟩
  rw [← nsmul_eq_mul, h]

theorem den_fin {ι : Type*} [Fintype ι] (x : ι → E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ i, IntE ((m : E) * x i) := by
  classical
  choose m hm hx using fun i => den_exists (x i)
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr (fun i _ => hm i), fun i => ?_⟩
  have : ((∏ j, m j : ℕ) : E) * x i = ((∏ j ∈ Finset.univ.erase i, m j : ℕ) : E) * ((m i : E) * x i) := by
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast; ring
  rw [this]
  exact intE_nat_mul _ (hx i)

theorem den_mat {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ i j, IntE ((k : E) * A i j) := by
  obtain ⟨k, hk, h⟩ := den_fin (fun p : m × n => A p.1 p.2)
  exact ⟨k, hk, fun i j => h (i, j)⟩

theorem intE_matmul {l m n : Type*} [Fintype m] {A : Matrix l m E} {B : Matrix m n E} {a b : ℕ}
    (hA : ∀ i j, IntE ((a : E) * A i j)) (hB : ∀ i j, IntE ((b : E) * B i j)) :
    ∀ i j, IntE (((a * b : ℕ) : E) * (A * B) i j) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine intE_sum _ _ fun k _ => ?_
  have : ((a * b : ℕ) : E) * (A i k * B k j) = ((a : E) * A i k) * ((b : E) * B k j) := by push_cast; ring
  rw [this]; exact intE_mul (hA i k) (hB k j)

end Den

section Lat

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem coe_smul_eq (o : 𝓞 E) (v : V) : (o : E) • v = o • v := algebraMap_smul E o v

theorem nat_smul_mem (Λ : Submodule (𝓞 E) V) (k : ℕ) {v : V} (hv : v ∈ Λ) : (k : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hv k

theorem int_smul_mem (Λ : Submodule (𝓞 E) V) {c : E} (hc : IntE c) {v : V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  rw [coe_smul_eq]; exact Λ.smul_mem o hv

theorem lat_smul_mem (Λ : Submodule (𝓞 E) V) (h : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  exact Bl.general_b_fact_third_version.goal1 Λ h v

theorem lat_fun_bdd (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) {ι : Type*} [Fintype ι]
    (φ : ι → V →ₗ[E] E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ v ∈ Λ, ∀ i, IntE ((m : E) * φ i v) := by
  classical
  obtain ⟨S, hS⟩ := h.fg
  obtain ⟨m, hm, hmS⟩ := den_fin (fun p : ι × S => φ p.1 (p.2 : V))
  refine ⟨m, hm, fun v hv i => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hmS (i, ⟨x, hx⟩)
  | zero => simpa using intE_zero
  | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact intE_add hx hy
  | smul o x _ hx =>
    rw [← coe_smul_eq, LinearMap.map_smul, smul_eq_mul, mul_left_comm]
    exact intE_mul ⟨o, rfl⟩ hx

theorem coord_exists [FiniteDimensional E V] {n : ℕ} {f : Fin n → V} (hf : LinearIndependent E f) :
    ∃ φ : Fin n → V →ₗ[E] E, ∀ c d, φ c (f d) = if d = c then 1 else 0 := by
  classical
  have : ∀ c : Fin n, ∃ G : V →ₗ[E] E, ∀ d, G (f d) = if d = c then 1 else 0 := by
    intro c
    obtain ⟨G, hG⟩ := LinearMap.exists_extend ((Finsupp.lapply c).comp hf.repr)
    refine ⟨G, fun d => ?_⟩
    have h1 : G (f d) = (G.comp (Submodule.span E (Set.range f)).subtype) ⟨f d, Submodule.subset_span ⟨d, rfl⟩⟩ := rfl
    rw [h1, hG]
    rw [LinearMap.comp_apply, hf.repr_eq_single d _ rfl, Finsupp.lapply_apply, Finsupp.single_apply]
  choose φ hφ using this
  exact ⟨φ, hφ⟩

end Lat

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end
end
