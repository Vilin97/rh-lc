module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PIdemCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLinFactor
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchStep
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatching
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLocal

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGaussLin

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.gaussLin_of :
    GaussLin := by
  intro A ι _ c s hs hc
  by_contra hc0
  have hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0 := by
    intro a
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hIt : (Submodule.span A {c}).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1:A) ∈ (Submodule.span A {c}).annihilator := by
      rw [h]; exact Submodule.mem_top
    rw [hmem, one_mul] at h1
    exact hc0 h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIt
  haveI := hM
  letI := Ideal.Quotient.field M
  have hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0 := by
    ext m
    change (MvPolynomial.map (Ideal.Quotient.mk M) s.prod).coeff m = 0
    rw [MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    apply hIM
    rw [hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc]
    rfl
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨p, hp, hp0⟩ := hprod
  obtain ⟨m, hm⟩ := hs p hp
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) hp0
  rw [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchPart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchPart_of :
    SameNormBasic → Matching → PermOfMap → MatchPart := by
  intro hSN hMatch hPerm B _ ϖ hϖ ι _ I I' _ _ N hI hI' u u' hsame e he hdiv hcmp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* B ⧸ Ideal.span {1 - e}, ρ = Ideal.Quotient.mk _ := ⟨_, rfl⟩
  have hsurj : Function.Surjective ρ := by
    subst hρ
    exact Ideal.Quotient.mk_surjective
  have hker : ∀ a b : B, ρ a = ρ b ↔ a - b ∈ Ideal.span {1 - e} := by
    subst hρ
    exact fun a b => Ideal.Quotient.eq
  have he' : e * e = e := he
  have hρe : ρ e = 1 := by
    rw [← map_one ρ]
    exact (hker e 1).mpr (Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩)
  have L1 : ∀ a b : B, ρ a = ρ b → e * a = e * b := by
    intro a b hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hker a b).mp hab)
    linear_combination (-e) * hc + (-c) * he'
  have L2 : ∀ a b : B, ρ a ∣ ρ b → a ∣ e * b := by
    rintro a b ⟨c', hc'⟩
    obtain ⟨c, rfl⟩ := hsurj c'
    rw [← map_mul] at hc'
    have := L1 _ _ hc'
    exact ⟨e * c, by rw [this]; ring⟩
  have L3 : ∀ a b : B, a ∣ e * b → ρ a ∣ ρ b := by
    intro a b h
    have := map_dvd ρ h
    rwa [map_mul, hρe, one_mul] at this
  by_cases hu : IsUnit (ρ ϖ)
  · obtain ⟨σ⟩ : Nonempty (I ≃ I') := ⟨Fintype.equivOfCardEq (hI.trans hI'.symm)⟩
    refine ⟨σ, fun i k => L2 _ _ hu.dvd⟩
  have hnzd : ρ ϖ ∈ nonZeroDivisors (B ⧸ Ideal.span {1 - e}) := by
    have hr : ∀ z' : B ⧸ Ideal.span {1 - e}, z' * ρ ϖ = 0 → z' = 0 := by
      intro z' hz'
      obtain ⟨z, rfl⟩ := hsurj z'
      rw [← map_mul, ← map_zero ρ] at hz'
      have h1 := L1 _ _ hz'
      have h2 : e * z * ϖ = 0 := by
        rw [mul_zero] at h1
        rw [mul_assoc]
        exact h1
      have h3 : e * z = 0 := (mem_nonZeroDivisors_iff.mp hϖ).2 _ h2
      rw [← one_mul (ρ z), ← hρe, ← map_mul, h3, map_zero]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => hr z (by rw [mul_comm]; exact hz), hr⟩
  have hle : Ideal.span {ϖ ^ (N + 1) ^ N} ≤ (Ideal.span {ρ ϖ ^ (N + 1) ^ N}).comap ρ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hsame' : SameNorm
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val))
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val)) := by
    have := (hSN (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ N}) ι).1 _ (Ideal.quotientMap _ ρ hle) _ _ hsame
    convert this using 1 <;>
      simp [redMod, Multiset.map_map, Function.comp_def, Ideal.quotientMap_mk]
  have hM := hMatch (B ⧸ Ideal.span {1 - e}) (ρ ϖ) hnzd hu ι N
    (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val)
    (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val) (by simp [hI]) (by simp [hI']) hsame' ?_ ?_
  · simp only [redMod, Multiset.map_map] at hM
    obtain ⟨σ, hσ⟩ := hPerm I I' _ _ _ hM
    refine ⟨σ, fun i k => ?_⟩
    have := congrFun (hσ i) k
    simp only [Function.comp_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub] at this
    exact L2 _ _ this
  · intro x hx y hy k k' hxy
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    rw [← map_sub, ← map_pow] at hxy
    rw [← map_sub, ← map_sub]
    rcases hcmp i i' k k' (L2 _ _ hxy) with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
  · intro x hx y hy k j hj
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    have hm : (N + 1) ^ j ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) hj
    rw [← map_sub, ← map_pow]
    rcases hdiv i i' k _ hm with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchVal_of :
    IdemCover → ValLocal → MatchPart → MatchingVal := by
  intro hC hL hP B _ ϖ hϖ hv ι _ I I' _ _ _ _ N hI hI' u u' hS
  classical
  let J : (I ≃ I') → Ideal B := fun σ =>
    { carrier := {b | ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k)}
      add_mem' := by
        intro a b ha hb i k
        rw [add_mul]
        exact dvd_add (ha i k) (hb i k)
      zero_mem' := by
        intro i k
        simp
      smul_mem' := by
        intro c b hb i k
        rw [smul_eq_mul, mul_assoc]
        exact Dvd.dvd.mul_left (hb i k) c }
  have hJ : ∀ σ b, b ∈ J σ ↔ ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k) := fun _ _ => Iff.rfl
  obtain ⟨e, he, hmem⟩ := hC B (I ≃ I') J (by
    intro 𝔪 h𝔪
    let D : Finset B := (Finset.univ : Finset (I × I' × ι)).image fun p => u p.1 p.2.2 - u' p.2.1 p.2.2
    have hD : ∀ i i' k, u i k - u' i' k ∈ D := fun i i' k =>
      Finset.mem_image.2 ⟨(i, i', k), Finset.mem_univ _, rfl⟩
    obtain ⟨e, hid, hnot, h1, h2⟩ := hL B ϖ hv 𝔪 h𝔪.isPrime D ((N + 1) ^ N)
    obtain ⟨σ, hσ⟩ := hP B ϖ hϖ ι I I' N hI hI' u u' hS e hid
      (fun i i' k m hm => h1 _ (hD i i' k) m hm)
      (fun i i' k k' h => h2 _ (hD i i' k) _ (hD i i' k') h)
    exact ⟨σ, e, (hJ σ e).2 hσ, hid, hnot⟩)
  exact ⟨e, he, fun σ i k => (hJ σ (e σ)).1 (hmem σ) i k⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPermMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
end
end

-- Source module: Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsMatchingOfSameNorm

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private theorem powHom_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) :
    ∃ φ : A.A →+* A.A, ∀ x, φ x = x ^ l ^ a := by
  induction a with
  | zero => exact ⟨RingHom.id _, fun x => by simp⟩
  | succ a ih =>
    obtain ⟨φ, hφ⟩ := ih
    refine ⟨A.frob.comp φ, fun x => ?_⟩
    rw [RingHom.comp_apply, hφ, pow_succ l a, pow_mul]
    rfl

private theorem root_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) (y : A.A) :
    ∃ w : A.A, w ^ l ^ a = y := by
  induction a generalizing y with
  | zero => exact ⟨y, by simp⟩
  | succ a ih =>
    obtain ⟨z, hz⟩ := (A.perf.bijective_frobenius).2 y
    obtain ⟨w, hw⟩ := ih z
    refine ⟨w, ?_⟩
    rw [pow_succ l a, pow_mul, hw]
    exact hz

theorem UpperTheory.exists_orthogonalIdempotents_matching_of_sameNorm :
    ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ (a : ℕ) {ι I I' : Type} [Fintype ι] [Fintype I] [Fintype I']
        [DecidableEq I] [DecidableEq I'] (N : ℕ), Fintype.card I = N → Fintype.card I' = N →
        (N + 1) ^ N ≤ l ^ a → ∀ (c : I → ι → Qb A) (c' : I' → ι → Qb A),
        SameNorm (Finset.univ.val.map c) (Finset.univ.val.map c') →
        ∃ e : (I ≃ I') → A.A, CompleteOrthogonalIdempotents e ∧ ∀ σ i k,
          (Ideal.Quotient.mk _ (e σ) : Qb A) * c i k ^ l ^ a = Ideal.Quotient.mk _ (e σ) * c' (σ i) k ^ l ^ a := by
  intro l _ A hA a ι I I' _ _ _ _ _ N hI hI' hN c c' h
  have hq : 0 < l ^ a := pow_pos (Fact.out : l.Prime).pos a
  obtain ⟨φ, hφ⟩ := powHom_exists A a
  obtain ⟨w, hw⟩ := root_exists A a A.pi
  have hwn : w ∈ nonZeroDivisors A.A := by
    have h1 : w ^ (l ^ a - 1) * w ∈ nonZeroDivisors A.A := by
      rw [← pow_succ, Nat.sub_add_cancel hq, hw]
      exact A.tf
    exact (mul_mem_nonZeroDivisors.1 h1).2
  have hv : ValLike w := by
    rintro f g ⟨m, hm⟩
    obtain ⟨e, he, h1, h2⟩ := hA.2 f g ⟨m, by
      rw [← hw, ← pow_mul, mul_comm, pow_mul]
      exact Ideal.pow_mem_of_mem _ hm _ hq⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩
  choose u hu using fun i k => Ideal.Quotient.mk_surjective (c i k)
  choose u' hu' using fun i k => Ideal.Quotient.mk_surjective (c' i k)
  have hdvd : w ^ (N + 1) ^ N ∣ A.pi := by
    rw [← hw]
    exact pow_dvd_pow w hN
  have hle : Ideal.span {A.pi} ≤ Ideal.span {w ^ (N + 1) ^ N} :=
    Ideal.span_singleton_le_span_singleton.2 hdvd
  have hsn : SameNorm (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u))
      (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u')) := by
    have h2 := (snBasic_of (Qb A) ι).1 (A.A ⧸ Ideal.span {w ^ (N + 1) ^ N}) (Ideal.Quotient.factor hle) _ _ h
    have e1 : ∀ {J : Type} [Fintype J] (v : J → ι → A.A) (d : J → ι → Qb A),
        (∀ i k, Ideal.Quotient.mk _ (v i k) = d i k) →
        (Finset.univ.val.map d).map (fun x k => Ideal.Quotient.factor hle (x k)) =
          redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map v) := by
      intro J _ v d hd
      rw [redMod, Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      funext k
      simp only [Function.comp_apply, ← hd i k]
      exact Ideal.Quotient.factor_mk hle _
    rw [← e1 u c hu, ← e1 u' c' hu']
    exact h2
  have MV : MatchingVal := matchVal_of idemCover_of valLocal_of
    (matchPart_of snBasic_of (matching_of snBasic_of (matchStep_of gaussLin_of snBasic_of linFactor_of)) permMap_of)
  obtain ⟨e, hce, he⟩ := MV A.A w hwn hv ι I I' N hI hI' u u' hsn
  refine ⟨e, hce, fun σ i k => ?_⟩
  obtain ⟨t, ht⟩ := he σ i k
  have hid : e σ ^ l ^ a = e σ := by
    have := (hce.idem σ).pow_succ_eq (l ^ a - 1)
    rwa [Nat.sub_add_cancel hq] at this
  have key : e σ * (u i k ^ l ^ a - u' (σ i) k ^ l ^ a) = A.pi * t ^ l ^ a := by
    have h3 := congrArg φ ht
    rw [map_mul, map_sub, map_mul, hφ, hφ, hφ, hφ, hφ, hid, hw] at h3
    exact h3
  rw [← hu i k, ← hu' (σ i) k, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨t ^ l ^ a, ?_⟩)
  rw [← mul_sub, key]
  rfl
end
end
