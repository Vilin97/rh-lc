module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Mathlib.Basic.Finite.Defs
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
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIffForallMaximalSpectrumResidueStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralResidueComapInvolutionIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusInvMulPowValuationNonnegIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitPrescribedResidueReducedFiniteAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusEqOneIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusSurjectiveStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolution

section

@[expose] public section

namespace GlobalTheory

theorem involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolutionStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_representatives_two_element_orbits_involution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  first | exact @GlobalTheory.involution_pair_representatives | exact GlobalTheory.involution_pair_representatives | (intros; apply GlobalTheory.involution_pair_representatives <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieReg

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieRegStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallInteger

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NotIntegral

theorem inv_small_not_integral : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  intro K B a ha m hint
  obtain ⟨ha0, hmax, -⟩ := ha
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let f : K.E →ₐ[K.O] (B.A ⧸ m.asIdeal) := IsScalarTower.toAlgHom K.O K.E (B.A ⧸ m.asIdeal)
  have hf : Function.Injective f := (algebraMap K.E (B.A ⧸ m.asIdeal)).injective
  have hE : IsIntegral K.O (algebraMap K.O K.E a)⁻¹ := (isIntegral_algHom_iff f hf).1 hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hE
  have hne : algebraMap K.O K.E a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]; exact ha0
  have hab : a * b = 1 := by
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  exact (IsLocalRing.mem_maximalIdeal a).1 hmax ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

end GlobalTheory.NotIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallIntegerStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.not_isIntegral_residue_inv_small_integer : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  first | exact @GlobalTheory.NotIntegral.inv_small_not_integral | exact GlobalTheory.NotIntegral.inv_small_not_integral | (intros; apply GlobalTheory.NotIntegral.inv_small_not_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegrality

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := GlobalTheory.T.isReduced_of_lieReg' K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs
  refine ⟨r, ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegralityStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  first | exact @GlobalTheory.UnitLemma.torus_mod_intUnits_structure | exact GlobalTheory.UnitLemma.torus_mod_intUnits_structure | (intros; apply GlobalTheory.UnitLemma.torus_mod_intUnits_structure <;> assumption)
end
end
