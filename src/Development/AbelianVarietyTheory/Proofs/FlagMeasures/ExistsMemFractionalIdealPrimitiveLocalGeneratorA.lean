module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOver

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOverStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' : ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | exact GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularLiftOfUnimodularMod

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_add_mul_notMem_of_maximal_ge {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J : Ideal R) (hJ : J ≠ 0) (n x : R)
    (h : ∀ p : Ideal R, p.IsMaximal → J ≤ p → n ∈ p → x ∉ p) :
    ∃ s : R, ∀ p : Ideal R, p.IsMaximal → J ≤ p → x + n * s ∉ p := by
  classical
  haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  let ι := {p : Ideal R // p.IsMaximal ∧ J ≤ p}
  haveI : Finite ι := Finite.of_injective
    (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J}))
    (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hc : Pairwise fun i j : ι => IsCoprime i.1 j.1 := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc
    (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))
  refine ⟨s, fun p hp hJp hmem => ?_⟩
  have h1 := Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)
  by_cases hx : x ∈ p
  · simp only [hx, if_true] at h1
    have h2 : n * s ∈ p := by simpa using p.sub_mem hmem hx
    have h3 : n ∈ p := by
      have := p.sub_mem h2 (p.mul_mem_left n h1)
      have e : n * s - n * (s - 1) = n := by ring
      rwa [e] at this
    exact h p hp hJp h3 hx
  · simp only [hx, if_false, sub_zero] at h1
    apply hx
    simpa using p.sub_mem hmem (p.mul_mem_left n h1)

theorem exists_unimodular_lift_of_unimodular_mod :
    ∀ (F : Type) [Field F] [NumberField F] (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), b ≠ 0 → ∀ (n x₀ : 𝓞 F) (y₀ : F), n ≠ 0 → y₀ ∈ b → (∀ p : Ideal (𝓞 F), p.IsMaximal → n ∈ p → ¬ (x₀ ∈ p ∧ y₀ ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b)) → ∃ (s : 𝓞 F) (t : F), t ∈ b ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → ¬ (x₀ + n * s ∈ p ∧ y₀ + (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b) := by
  intro F _ _ b hb n x₀ y₀ hn hy₀ H
  have hnF : (n : F) ≠ 0 := by
    intro e
    exact hn (RingOfIntegers.ext e)
  obtain ⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by
    by_cases h0 : y₀ = 0
    · obtain ⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hb (FractionalIdeal.eq_zero_iff.2 hcon)
      exact ⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩
    · exact ⟨0, b.zero_mem, by simpa using h0⟩
  set y := y₀ + (n : F) * t with hydef
  have hyb : y ∈ b := by
    have h1 : n • t ∈ (b : Submodule (𝓞 F) F) := Submodule.smul_mem _ n ht
    exact Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hb]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hy
    rw [← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]
    simp
  have key : ∀ p : Ideal (𝓞 F),
      y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p := by
    intro p
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]
    constructor
    · intro h
      have := mul_le_mul_left h b⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ] at this
    · intro h
      rw [← hJb]
      exact mul_le_mul_left h b
  obtain ⟨s, hs⟩ := exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by
    intro p hp hJp hnp hx
    refine H p hp hnp ⟨hx, ?_⟩
    have h1 := (key p).2 hJp
    have h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht
    have h3 := Submodule.sub_mem
      (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2
    have e : y - (n : F) * t = y₀ := by rw [hydef]; ring
    rw [e] at h3
    exact h3)
  exact ⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealPrimitiveLocalGeneratorA

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory
open Formalism.L2.SG.Pf.LatEx

theorem fractionalIdeal_restrictScalars_isLattice_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    Submodule.IsLattice F ((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) := by
  refine ⟨?_, ?_⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl c).restrictScalars
  · obtain ⟨x, hxc, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (c : Submodule (𝓞 E) E))
      (by rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot])
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem exists_basis_latSpanV_eq_of_finrank_two (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (hE : Module.finrank F E = 2) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    ∃ (e : Fin 2 → E) (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), LinearIndependent F e ∧ b ≠ 0 ∧
      (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b) e := by
  have hL := fractionalIdeal_restrictScalars_isLattice_of_tower F E c hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
  have hfull : Submodule.IsFullLattice F ((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) := by
    letI := hL
    refine ⟨?_⟩
    apply top_le_iff.mp
    intro z _
    obtain ⟨x, hxc, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (c : Submodule (𝓞 E) E))
      (by rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot])
    obtain ⟨n, hn, hi⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (z / x))).exists_integral_multiple
    let y : 𝓞 E := ⟨n • (z / x), hi⟩
    have hym : (y : E) * x ∈ (c : Submodule (𝓞 E) E) :=
      (c : Submodule (𝓞 E) E).smul_mem y hxc
    have hs : (n : F) • z ∈ Submodule.span F
        (((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) : Set E) := by
      apply Submodule.subset_span
      convert hym using 1
      simp [y, Algebra.smul_def, div_eq_mul_inv, hx0, mul_assoc]
    have hnF : (n : F) ≠ 0 := Int.cast_ne_zero.mpr hn
    have := (Submodule.span F (((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) : Set E)).smul_mem (n : F)⁻¹ hs
    simpa [smul_smul, hnF] using this
  let w := Module.finBasisOfFinrankEq F E hE
  obtain ⟨e, b, he, -, hb, heq⟩ := satBasisV_holds F E _ hfull 1 w w.linearIndependent (fun _ => 1)
    (fun _ => one_ne_zero)
  refine ⟨e, b, he, hb, ?_⟩
  rw [← heq, w.span_eq]
  simp

theorem basis_repr_mem_of_mem_latSpanV_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {z : E} (hz : z ∈ latSpanV C B) (i : Fin 2) : B.repr z i ∈ C i := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, x, hx, rfl⟩ := hy
    rw [map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; simpa using hx
    · rw [smul_zero]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | zero => rw [map_zero, Finsupp.zero_apply]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add (f := _), Finsupp.add_apply]; exact (C i : Submodule (𝓞 F) F).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, algebraMap_smul]
    exact (C i : Submodule (𝓞 F) F).smul_mem r hx

theorem algebraMap_ringOfIntegers_tower_mul_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (π : 𝓞 F) (z : E) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z = (algebraMap (𝓞 F) F π) • z := by
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem basis_repr_mem_of_mem_map_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) (i : Fin 2) :
    B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i := by
  let T : Submodule (𝓞 F) F := (↑((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) : Submodule (𝓞 F) F)
  have hcoord : ∀ z ∈ c, B.repr z i ∈ C i := fun z hz =>
    basis_repr_mem_of_mem_latSpanV_two B C (by rw [← hc]; exact hz) i
  have hgen : ∀ π ∈ p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z) i ∈ T := by
    intro π hπ z hz
    rw [algebraMap_ringOfIntegers_tower_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hπ) (hcoord z hz)
  have hq : ∀ q ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E q * z) i ∈ T := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨π, hπ, rfl⟩ := hy
      exact hgen π hπ
    | zero => intro z _; simp [T.zero_mem]
    | add x y _ _ hx hy =>
      intro z hz; rw [map_add (f := _), add_mul, map_add (f := _), Finsupp.add_apply]; exact T.add_mem (hx z hz) (hy z hz)
    | smul r x _ hx =>
      intro z hz
      have e1 : algebraMap (𝓞 E) E (r * x) * z = algebraMap (𝓞 E) E x * (algebraMap (𝓞 E) E r * z) := by
        rw [RingHom.map_mul]; ring
      rw [smul_eq_mul, e1]
      exact hx _ ((c : Submodule (𝓞 E) E).smul_mem r hz)
  refine FractionalIdeal.mul_induction_on (C := fun a => B.repr a i ∈ T) ha ?_ ?_
  · intro u hu z hz
    obtain ⟨q, hq', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
    exact hq q hq' z hz
  · intro x y hx hy
    simp only [map_add (f := _), Finsupp.add_apply]
    exact T.add_mem hx hy

theorem mem_map_mul_of_basis_repr_mem_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : ∀ i, B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) :
    a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  let M : Submodule (𝓞 E) E := (↑(((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E)
  have hterm : ∀ i, B.repr a i • B i ∈ M := by
    intro i
    refine FractionalIdeal.mul_induction_on (C := fun u => u • B i ∈ M) (ha i) ?_ ?_
    · intro u hu x hx
      obtain ⟨π, hπ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
      have hxc : x • B i ∈ c := by
        have : x • B i ∈ latSpanV C B := Submodule.subset_span ⟨i, x, hx, rfl⟩
        rw [← hc] at this; exact this
      show (algebraMap (𝓞 F) F π * x) • B i ∈ M
      rw [mul_smul, ← algebraMap_ringOfIntegers_tower_mul_eq_smul]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _
        (Ideal.mem_map_of_mem _ hπ)) hxc
    · intro x y hx hy
      show (x + y) • B i ∈ M
      rw [add_smul]; exact M.add_mem hx hy
  have hsum := B.sum_repr a
  rw [Fin.sum_univ_two] at hsum
  show a ∈ M
  rw [← hsum]
  exact M.add_mem (hterm 0) (hterm 1)

theorem exists_mem_fractionalIdeal_primitive_local_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro F E _ _ _ _ _ hE c hc N hN
  obtain ⟨e, b, he, hb, hce⟩ := exists_basis_latSpanV_eq_of_finrank_two F E hE c hc
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank he (by simp [hE])
  have hBe : ⇑B = e := coe_basisOfLinearIndependentOfCardEqFinrank he _
  let C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F := Fin.snoc (n := 1) (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b
  have hc' : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B := by rw [hBe]; exact hce
  have hC0 : C 0 = 1 := rfl
  have hC1 : C 1 = b := rfl
  have hspanN : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hm0 : Ideal.absNorm (Ideal.span {N}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hmN : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : 𝓞 E) ∈ Ideal.span {N} := Ideal.absNorm_mem _
  set m := Ideal.absNorm (Ideal.span {N})
  obtain ⟨a₀, ha₀c, ha₀⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' E c hc (m : 𝓞 E) (Nat.cast_ne_zero.mpr hm0)
  have hco : ∀ i, B.repr a₀ i ∈ C i := fun i =>
    basis_repr_mem_of_mem_latSpanV_two B C (show a₀ ∈ latSpanV C B by rw [← hc']; exact ha₀c) i
  obtain ⟨x₀, hx₀⟩ := (FractionalIdeal.mem_one_iff _).mp (hC0 ▸ hco 0)
  have hy₀ : B.repr a₀ 1 ∈ b := hC1 ▸ hco 1
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hmono : ∀ (I J : Ideal (𝓞 E)), I ≤ J → (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤
      (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro I J hIJ
    have : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := (FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hIJ
    gcongr
  obtain ⟨s, t, ht, hst⟩ := GlobalTheory.exists_unimodular_lift_of_unimodular_mod F b hb (m : 𝓞 F) x₀ (B.repr a₀ 1)
    (Nat.cast_ne_zero.mpr hm0) hy₀ (by
      rintro p hp hnp ⟨hxp, hyp⟩
      have hmem := mem_map_mul_of_basis_repr_mem_two B C c hc' p (a := a₀) (by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · rw [← hx₀, hC0, mul_one]; exact FractionalIdeal.mem_coeIdeal_of_mem _ hxp
        · exact hyp)
      obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ Q := Ideal.map_le_iff_le_comap.mpr hQp.ge
      have hmQ : (m : 𝓞 E) ∈ Q := hle (by
        rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E)) m]; exact Ideal.mem_map_of_mem _ hnp)
      exact ha₀ Q hQ hmQ (hmono _ _ hle hmem))
  let w : E := (algebraMap (𝓞 F) F s) • B 0 + t • B 1
  have hw : w ∈ c := by
    have : w ∈ latSpanV C B := Submodule.add_mem _
      (Submodule.subset_span ⟨0, _, (FractionalIdeal.mem_one_iff _).mpr ⟨s, rfl⟩, rfl⟩)
      (Submodule.subset_span ⟨1, t, ht, rfl⟩)
    rw [← hc'] at this; exact this
  have hmw : (m : F) • w = algebraMap (𝓞 E) E (m : 𝓞 E) * w := by
    rw [map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  refine ⟨a₀ + (m : F) • w, ?_, ?_, ?_⟩
  · rw [hmw]; exact (c : Submodule (𝓞 E) E).add_mem ha₀c ((c : Submodule (𝓞 E) E).smul_mem _ hw)
  · intro Q hQ hNQ ha
    have hmQ : (m : 𝓞 E) ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hNQ hmN
    have h2 : (m : F) • w ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hmw]; exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hmQ) hw
    refine ha₀ Q hQ hmQ ?_
    have e2 : a₀ = (a₀ + (m : F) • w) - (m : F) • w := by abel
    rw [e2]
    exact Submodule.sub_mem (↑((Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E) ha h2
  · intro p hp ha
    have h := basis_repr_mem_of_mem_map_mul_two B C c hc' p ha
    have hr : ∀ i, B.repr (a₀ + (m : F) • w) i = B.repr a₀ i + (m : F) * ((algebraMap (𝓞 F) F s) *
        (Finsupp.single 0 1 : Fin 2 →₀ F) i + t * (Finsupp.single 1 1 : Fin 2 →₀ F) i) := by
      intro i
      simp only [w, map_add (f := _), map_smul, B.repr_self, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    refine hst p hp ⟨?_, ?_⟩
    · have h0 := h 0
      rw [hC0, mul_one, hr 0] at h0
      obtain ⟨x', hx'p, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h0
      have : x' = x₀ + (m : 𝓞 F) * s := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [hx', map_add (f := _), map_mul, map_natCast, hx₀]
        simp
      exact this ▸ hx'p
    · have h1 := h 1
      rw [hC1, hr 1] at h1
      convert h1 using 1
      simp

end GlobalTheory
end
end
