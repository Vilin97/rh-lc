module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
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
import Mathlib.RingTheory.Unramified.LocalStructure
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
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
public import Mathlib.Dynamics.Newton
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeTensorPolynomialIsMaximalOfMemImageStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationPowSurj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingLieInjective

section

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory

theorem genFibre_prime_meets_polynomial :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  intro T _ _ _ hA O _ _ _ _ _ _ hind P hP hne
  haveI : IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) :=
    (locIndEtale_isDomain_isIntegrallyClosed T O 1 ⟨inferInstance, hA⟩ (by simp) one_pos hind).1
  by_contra hcon
  push_neg at hcon

  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) y
  have ho : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o = IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s :=
    (IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s).symm
  have hoP : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ∈ P := ho ▸ P.mul_mem_right _ hyP
  have ho0 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ≠ 0 := by
    rw [ho]
    exact mul_ne_zero hy0 (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s).ne_zero
  obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hind
  obtain ⟨i, hoi⟩ := hcov o
  obtain ⟨E, _, _, _, p, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite (Polynomial T) (Localization.AtPrime p) := inferInstance
  haveI : Algebra.QuasiFinite (Polynomial T) (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).1 this
  let φ : Si i →+* (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := (algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comp (Si i).val.toRingHom
  have hφ : ∀ g : Polynomial T, φ (algebraMap (Polynomial T) (Si i) g) =
      algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g := fun g => by
    simp [φ, IsScalarTower.algebraMap_apply (Polynomial T) O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))]
  haveI h1 : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P
  haveI h0 : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).IsPrime := Ideal.comap_isPrime φ ⊥
  have hunder : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).under (Polynomial T) = (P.comap φ).under (Polynomial T) := by
    ext g
    simp only [Ideal.under, Ideal.mem_comap, hφ, Ideal.mem_bot]
    constructor
    · intro h; rw [h]; exact P.zero_mem
    · intro h
      by_cases hg : g = 0
      · rw [hg, map_zero]
      · exact absurd h (hcon g hg)
  have heq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial T) _ _
    (Ideal.comap_mono bot_le) hunder
  have hmem : (⟨o, hoi⟩ : Si i) ∈ P.comap φ := hoP
  rw [← heq, Ideal.mem_comap, Ideal.mem_bot] at hmem
  exact ho0 hmem

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPolynomialMemPrimeLocalization

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  first | (exact @GlobalTheory.genFibre_prime_meets_polynomial) | (exact GlobalTheory.genFibre_prime_meets_polynomial) | (intros; apply GlobalTheory.genFibre_prime_meets_polynomial  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensional

section

@[expose] public section

namespace GlobalTheory

theorem pow_idempotent_combination {R : Type} [CommRing R] {g : R} (hg : IsIdempotentElem g)
    (a b : R) (n : ℕ) : (g * a + (1 - g) * b) ^ n = g * a ^ n + (1 - g) * b ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    linear_combination (a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq

theorem exists_unit_pow_eq_of_krullDimLE_zero : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R]
    (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ,
    (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  intro R _ _ q hq hqu u hloc
  have hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal := fun P hP => hP.isMaximal'
  let S : Set R := {g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}
  have hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S := by
    rintro g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩
    refine ⟨?_, g * x + (1 - g) * z, ?_⟩
    · show (g + h - g * h) * (g + h - g * h) = g + h - g * h
      linear_combination (1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq
    · have key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u)
          = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u)) := by
        rw [pow_idempotent_combination hg]
        linear_combination (x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq
      rw [key]
      exact Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))
  have hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨x, hx⟩ := hloc m hm
    obtain ⟨e, b, he, hab, hep⟩ := exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)
    refine ⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩
    · rw [nilpotent_iff_mem_prime]
      intro p hp
      by_cases ha : x ^ q - (u : R) ∈ p
      · exact p.mul_mem_left _ ha
      · have hep' := hep p hp ha
        have h0 : e * (1 - e) ∈ p := by
          have : e * (1 - e) = 0 := by linear_combination -he.eq
          rw [this]; exact p.zero_mem
        rcases hp.mem_or_mem h0 with h | h
        · exact absurd h hep'
        · exact p.mul_mem_right _ h
    · intro h
      have hem : e ∈ m := hab ▸ m.mul_mem_right b hx
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using m.add_mem h hem
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgS, hgm⟩ := hcover m hm
    exact hgm (hle (Ideal.subset_span hgS))
  have hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haS : a ∈ S := hT (by simp)
      obtain ⟨G, hG, hGT⟩ := ih (fun y hy => hT (by simp [hy]))
      refine ⟨a + G - a * G, hjoin a haS G hG, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · linear_combination (1 - G) * haS.1.eq
      · have := hGT g hg
        linear_combination (1 - a) * this
  have h1 : (1 : R) ∈ Ideal.span S := by rw [hspan]; trivial
  obtain ⟨n, f, g, hf⟩ := Submodule.mem_span_set'.mp h1
  classical
  obtain ⟨G, hG, hGT⟩ := hfin (Finset.univ.image fun i => (g i : R)) (by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (g i).2)
  have hG1 : G = 1 := by
    have : (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [hf, one_mul] at this
    exact this
  obtain ⟨x, hx⟩ := hG.2
  rw [hG1, one_mul] at hx
  have hxq : IsUnit (x ^ q) := by
    have := hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
    simpa using this
  have hxu : IsUnit x := (isUnit_pow_iff hq.ne').mp hxq
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.C (u : R)
  have hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u := by
    intro y; simp [P]
  have hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1) := by
    simp [P, Polynomial.derivative_X_pow]
  obtain ⟨v, ⟨-, hv⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x)
    (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))
  rw [hP, sub_eq_zero] at hv
  have hvu : IsUnit v := (isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)
  exact ⟨hvu.unit, Units.ext (by simp [hv])⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensionalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_root_of_unit_zero_dimensional : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R] (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ, (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  first | (exact @GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (exact GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (intros; apply GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebras

section

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory.QUnits

theorem tensorFractionRing_units_pow_surj : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ u
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let R := TensorProduct T (FractionRing T) A
  let f : O →+* R := (Algebra.TensorProduct.includeRight : A →ₐ[T] R).toRingHom.comp π.toRingHom
  have hπT : ∀ t : T, π (algebraMap T O t) = algebraMap T A t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hfT : ∀ t : T, f (algebraMap T O t) = algebraMap T R t := by
    intro t
    change Algebra.TensorProduct.includeRight (π (algebraMap T O t)) = _
    rw [hπT, AlgHom.commutes]
  have hf : ∀ y : Algebra.algebraMapSubmonoid O (nonZeroDivisors T), IsUnit (f y) := by
    rintro ⟨_, t, ht, rfl⟩
    change IsUnit (f (algebraMap T O t))
    rw [hfT, IsScalarTower.algebraMap_apply T (FractionRing T) R]
    exact (IsLocalization.map_units (FractionRing T) ⟨t, ht⟩).map _
  let φ : L →+* R := IsLocalization.lift hf
  have hφ : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero φ⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add φ a b⟩
    | tmul k a =>
      obtain ⟨o, rfl⟩ := hπ a
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) k
      refine ⟨IsLocalization.mk' L (algebraMap T O x * o)
        (⟨algebraMap T O s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ :
          Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ?_⟩
      rw [IsLocalization.lift_mk'_spec]
      change f (algebraMap T O x * o) = f (algebraMap T O (s : T)) * _
      rw [map_mul, hfT, hfT]
      change algebraMap T R x * (Algebra.TensorProduct.includeRight (π o)) = _
      have hR : ∀ t : T, algebraMap T R t = algebraMap T (FractionRing T) t ⊗ₜ[T] (1 : A) := fun t => rfl
      rw [Algebra.TensorProduct.includeRight_apply, hR, hR, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, IsLocalization.mk'_spec']
  have hB : ∀ P : Ideal L, P.IsPrime → P ≠ ⊥ → P.IsMaximal ∧ ∀ x : L, ∃ c d : T, d ≠ 0 ∧
      algebraMap T L d * x - algebraMap T L c ∈ P := by
    intro P hP hne
    obtain ⟨g, hg, hgP⟩ := GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization T hAIC O hind P hP hne
    exact GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image T hAIC O hind P hP g hg hgP
  by_cases hJ : RingHom.ker φ = ⊥
  · have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hJ
    let e : L ≃+* R := RingEquiv.ofBijective φ ⟨hinj, hφ⟩
    obtain ⟨v, hv⟩ := GlobalTheory.LocAcycUnits.units_localization_pow_surj T O q ⟨inferInstance, hAIC⟩ hq hq0
      hind (Units.map e.symm.toMonoidHom u)
    refine ⟨Units.map e.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]; ext; simp
  · let J := RingHom.ker φ
    let e : L ⧸ J ≃+* R := RingHom.quotientKerEquivOfSurjective hφ
    have hne : ∀ I : Ideal (L ⧸ J), I.comap (Ideal.Quotient.mk J) ≠ ⊥ := by
      intro I h
      apply hJ
      rw [eq_bot_iff]
      intro x hx
      rw [← h, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact I.zero_mem
    haveI : Ring.KrullDimLE 0 (L ⧸ J) := by
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have hP : (I.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      have hmax := (hB _ hP (hne I)).1
      have := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hmax
      rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at this
      exact this.resolve_left hI.ne_top
    have hqL : IsUnit (q : L ⧸ J) := by
      have := hq.map (algebraMap T (L ⧸ J)); simpa using this
    have hroot : ∀ m : Ideal (L ⧸ J), m.IsMaximal → ∃ x : L ⧸ J,
        x ^ q - ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J) ∈ m := by
      intro m hm
      obtain ⟨w0, hw0⟩ := Ideal.Quotient.mk_surjective
        ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J)
      have hP : (m.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨c, d, hd, hcd⟩ := (hB _ hP (hne m)).2 w0
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hAIC (Polynomial.X ^ (n + 1) - Polynomial.C (c * d ^ n))
        (Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero n))
        (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hq0)
      have hrq : r ^ (n + 1) = c * d ^ n := by simpa [sub_eq_zero] using hr
      have hdu : IsUnit (algebraMap T L d) := by
        rw [IsScalarTower.algebraMap_apply T O L]
        exact IsLocalization.map_units L (⟨algebraMap T O d,
          Algebra.mem_algebraMapSubmonoid_of_mem (⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ :
            nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      set D := algebraMap T L d
      set Dinv : L := ((hdu.unit⁻¹ : Lˣ) : L)
      have hDn : Dinv ^ (n + 1) * D ^ (n + 1) = 1 := by
        rw [← mul_pow, IsUnit.val_inv_mul, one_pow]
      have hR : algebraMap T L r ^ (n + 1) = algebraMap T L c * D ^ n := by
        rw [← map_pow, hrq, map_mul, map_pow]
      refine ⟨Ideal.Quotient.mk J (algebraMap T L r * Dinv), ?_⟩
      rw [← hw0, ← map_pow, ← map_sub, ← Ideal.mem_comap]
      have key : (algebraMap T L r * Dinv) ^ (n + 1) - w0 =
          -(Dinv ^ (n + 1) * D ^ n) * (D * w0 - algebraMap T L c) := by
        linear_combination Dinv ^ (n + 1) * hR + w0 * hDn
      rw [key]
      exact Ideal.mul_mem_left _ _ hcd
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_root_of_unit_zero_dimensional (L ⧸ J) q hq0 hqL (Units.map e.symm.toMonoidHom u) hroot
    exact ⟨Units.map e.toMonoidHom v, by rw [← map_pow, hv]; ext; simp⟩

end GlobalTheory.QUnits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebrasStatement

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.henselian_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  first | (exact @GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (exact GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (intros; apply GlobalTheory.QUnits.tensorFractionRing_units_pow_surj  <;> assumption)
end
end
