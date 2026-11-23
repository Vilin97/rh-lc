module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIsDomainIsIntegrallyClosed
public import Mathlib.RingTheory.Etale.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivial
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIncomparability

section

@[expose] public section

namespace GlobalTheory

theorem eq_of_le_of_comap_eq_of_indEtale : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  intro B O _ _ _ ⟨ι, _, _, _, Si, _, hcov, hloc⟩ p p' hp hp' hle hcomap
  by_contra hne
  obtain ⟨x, hx', hx⟩ : ∃ x, x ∈ p' ∧ x ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨E, _, _, _, P, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite B (Localization.AtPrime P) := inferInstance
  haveI : Algebra.QuasiFinite B (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have key := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := B)
    (p.comap (algebraMap (Si i) O)) (p'.comap (algebraMap (Si i) O)) (Ideal.comap_mono hle)
    (by
      simp only [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hcomap)
  have h1 : (⟨x, hi⟩ : Si i) ∈ p'.comap (algebraMap (Si i) O) := hx'
  rw [← key] at h1
  exact hx h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtalePrimeComparison

section

@[expose] public section


theorem _root_.GlobalTheory.T.ind_etale_prime_comparison : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  first | (exact @GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (exact GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (intros; apply GlobalTheory.eq_of_le_of_comap_eq_of_indEtale  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.pic_eq_one_of_forall_prime_maximal : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := by
  first | (exact @GlobalTheory.pic_eq_one_of_forall_isMaximal) | (exact GlobalTheory.pic_eq_one_of_forall_isMaximal) | (intros; apply GlobalTheory.pic_eq_one_of_forall_isMaximal  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneIsUnitOneSubPow

section

@[expose] public section

namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicLocalizationStrictHenselisationNoTorsion

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicGenericFibreQuotientStrictHenselisationNoTors

section

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory.QPic

theorem pic0 : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := GlobalTheory.T.pic_eq_one_of_forall_prime_maximal

theorem incomp : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := GlobalTheory.T.ind_etale_prime_comparison

theorem poly : ∀ (T : Type) [CommRing T] [IsDomain T] (P P' : Ideal (Polynomial T)), P.IsPrime → P'.IsPrime → P ≤ P' → P ≠ ⊥ → P'.comap (algebraMap T (Polynomial T)) = ⊥ → P = P' := by
  intro T _ _ P P' hP hP' hle h0 hC
  let K := FractionRing T
  letI : Algebra (Polynomial T) (Polynomial K) := Polynomial.algebra T K
  haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors T)) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors T) K
  set M := Submonoid.map Polynomial.C (nonZeroDivisors T) with hM
  have hdisj' : Disjoint (M : Set (Polynomial T)) (P' : Set (Polynomial T)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    have : s ∈ P'.comap (algebraMap T (Polynomial T)) := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hsP
    rw [hC, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hs this
  have hdisj : Disjoint (M : Set (Polynomial T)) (P : Set (Polynomial T)) :=
    hdisj'.mono_right hle
  have hPK := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P hP hdisj
  have hP'K := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P' hP' hdisj'
  have hc := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP hdisj
  have hc' := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP' hdisj'
  have hM0 : (0 : Polynomial T) ∉ M := by
    intro h
    obtain ⟨s, hs, hs0⟩ := Submonoid.mem_map.mp h
    exact nonZeroDivisors.ne_zero hs (Polynomial.C_eq_zero.mp hs0)
  have hne : P.map (algebraMap (Polynomial T) (Polynomial K)) ≠ ⊥ := by
    intro hb
    apply h0
    rw [← hc, hb, eq_bot_iff]
    intro x hx0
    have hx : algebraMap (Polynomial T) (Polynomial K) x = 0 := (Ideal.mem_bot).mp hx0
    exact (Ideal.mem_bot).mpr (IsLocalization.injective (Polynomial K) (le_nonZeroDivisors_of_noZeroDivisors hM0)
      (hx.trans (map_zero _).symm))
  have hmax : (P.map (algebraMap (Polynomial T) (Polynomial K))).IsMaximal := hPK.isMaximal hne
  have heq := hmax.eq_of_le hP'K.ne_top (Ideal.map_mono hle)
  rw [← hc, ← hc', heq]

theorem pic_transfer {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (q : ℕ)
    (h : ∀ c : CommRing.Pic S, c ^ q = 1 → c = 1) (c : CommRing.Pic R) (hc : c ^ q = 1) : c = 1 := by
  have h1 : CommRing.Pic.mapRingHom e.toRingHom c = 1 := h _ (by rw [← map_pow, hc, map_one])
  have h2 : CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom c) = c := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]
  rw [← h2, h1, map_one]

theorem primes_eq (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (hind : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i))
    (p p' : Ideal O) [p.IsPrime] [p'.IsPrime] (hle : p ≤ p') (h0 : p ≠ ⊥)
    (hT : p'.comap (algebraMap T O) = ⊥) : p = p' := by
  have hinc := incomp (Polynomial T) O hind
  refine hinc p p' inferInstance inferInstance hle ?_
  refine poly T _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (Ideal.comap_mono hle) ?_ ?_
  · intro hb
    have : (⊥ : Ideal O).comap (algebraMap (Polynomial T) O) = p.comap (algebraMap (Polynomial T) O) := by
      apply le_antisymm (Ideal.comap_mono bot_le); rw [hb]; exact bot_le
    exact h0 (hinc ⊥ p Ideal.isPrime_bot inferInstance bot_le this).symm
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hT

end GlobalTheory.QPic


open GlobalTheory.QPic in
theorem GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ c hc
  haveI : IsIntegrallyClosed T := GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hAIC
  haveI : IsDomain O := (GlobalTheory.indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind).1
  let eA := Localization.tensorRightAlgEquiv (nonZeroDivisors T) A
  by_cases hI : RingHom.ker (π : O →+* A) = ⊥
  · have hinj : Function.Injective π := (RingHom.injective_iff_ker_eq_bot _).mpr hI
    let eπ : O ≃ₐ[T] A := AlgEquiv.ofBijective (π.restrictScalars T) ⟨hinj, hπ⟩
    let e1 : TensorProduct T (FractionRing T) A ≃ₐ[T] TensorProduct T (FractionRing T) O :=
      Algebra.TensorProduct.congr AlgEquiv.refl eπ.symm
    let e2 := Localization.tensorRightAlgEquiv (nonZeroDivisors T) O
    refine pic_transfer (e1.toRingEquiv.trans e2.toRingEquiv) q ?_ c hc
    exact GlobalTheory.pic_localization_strictHenselisation_no_torsion T O q ⟨inferInstance, hAIC⟩ hq
      (Nat.pos_of_ne_zero (NeZero.ne q)) hind
  · refine pic_transfer eA.toRingEquiv q (fun c' _ => pic0 _ ?_ c') c hc
    intro Q hQ
    obtain ⟨Q', hQ'max, hle⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    suffices hQQ : Q = Q' by rw [hQQ]; exact hQ'max
    set L := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
    have hQ'p : Q'.IsPrime := hQ'max.isPrime
    set p := (Q.comap (algebraMap A L)).comap (π : O →+* A) with hpdef
    set p' := (Q'.comap (algebraMap A L)).comap (π : O →+* A) with hp'def
    have hpp : p = p' := by
      refine primes_eq T O hind p p' (Ideal.comap_mono (Ideal.comap_mono hle)) ?_ ?_
      · intro hb
        apply hI
        rw [eq_bot_iff, ← hb]
        intro x hx
        rw [RingHom.mem_ker] at hx
        simp [hpdef, hx]
      · rw [eq_bot_iff]
        intro t ht
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap] at ht
        rw [Ideal.mem_bot]
        by_contra ht0
        have hcomm : (π : O →+* A) (algebraMap T O t) = algebraMap T A t := by
          rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, IsScalarTower.algebraMap_apply T (Polynomial T) A]
          exact π.commutes _
        rw [hcomm] at ht
        have hu : IsUnit (algebraMap A L (algebraMap T A t)) :=
          IsLocalization.map_units L (⟨algebraMap T A t, t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩ :
            Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
        exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ ht hu)
    have hqq : Q.comap (algebraMap A L) = Q'.comap (algebraMap A L) := by
      rw [← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q.comap (algebraMap A L)),
        ← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q'.comap (algebraMap A L))]
      exact congrArg _ hpp
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q,
      ← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q']
    exact congrArg (Ideal.map (algebraMap A L)) hqq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicGenericFibreQuotientStrictHenselisationNoTorsStatement

section

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  first | (exact @GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (exact GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (intros; apply GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion  <;> assumption)
end
end
