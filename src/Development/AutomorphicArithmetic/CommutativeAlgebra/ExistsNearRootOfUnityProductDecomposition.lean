module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFactorizationNearRootOfUnityHenselian
public import Mathlib.Algebra.Polynomial.Laurent
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
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartAdjoinRootLaurent
public import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityLiftModNilpotentUnique
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicLaurentPolynomialNearRootOfUnity

section

@[expose] public section

noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity :
    ∀ (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Int → ∀ (q : ℕ), 0 < q → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ (φ : LaurentPolynomial A →ₐ[A] D) (P : Polynomial (LaurentPolynomial A)) (n : ℕ), φ (LaurentPolynomial.T 1) = T.t ∧ φ (LaurentPolynomial.T (-1)) = T.s ∧ P.Monic ∧ P.eval₂ φ.toRingHom w = 0 ∧
        ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) := by
  intro A D _ _ _ _ T hI q hq w hw
  classical
  let τ : Dˣ := ⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩
  let φ0 : LaurentPolynomial A →+* D := LaurentPolynomial.eval₂ (algebraMap A D) τ
  have hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a := by
    intro a
    simp [φ0, LaurentPolynomial.algebraMap_apply]
  let φ : LaurentPolynomial A →ₐ[A] D := { φ0 with commutes' := hcomm }
  have ht : φ (LaurentPolynomial.T 1) = T.t := by
    change φ0 _ = _
    simp [φ0, τ]
  have hs : φ (LaurentPolynomial.T (-1)) = T.s := by
    change φ0 _ = _
    simp [φ0, τ, zpow_neg]
  letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r := fun _ => rfl
  have hadj : Algebra.adjoin A {T.t} ≤ φ.range := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨_, ht⟩
  have hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b := by
    intro b hb
    obtain ⟨p, hpm, hp0⟩ := hI.1 b hb
    have hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈
        Polynomial.lifts (algebraMap (LaurentPolynomial A) D) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hadj (p.coeff n).2
      exact ⟨r, hr⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
    exact hp0
  have hint : Algebra.IsIntegral (LaurentPolynomial A) D := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, hk⟩ := T.locB x
    have hsI : IsIntegral (LaurentPolynomial A) T.s := by
      rw [← hs]
      exact isIntegral_algebraMap
    have : x = T.s ^ k * (T.t ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]
    rw [this]
    exact (hsI.pow k).mul (hB _ hk)
  have hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D)
      ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) := by
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha d _
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a) := by
        rw [hmap]
        exact (hcomm a).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
  obtain ⟨Q, hQm, hQ0, hQc⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu
  set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef
  have hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'
  have hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0 := by
    have := Polynomial.natDegree_X_pow_sub_C (n := q) (1 : LaurentPolynomial A)
    rw [map_one] at this
    rw [this]
    exact hq.ne'
  refine ⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩
  · rw [Polynomial.eval₂_comp]
    have : Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1 := by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
    rw [this]
    exact hQ0
  · intro i
    have hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I := by
      intro j
      by_cases hj : j = Q.natDegree
      · subst hj
        have : Q.coeff Q.natDegree = 1 := hQm
        simp [this]
      · simpa [Polynomial.coeff_X_pow, hj] using hQc j hj
    have heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree =
        (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1) := by
      simp [Polynomial.sub_comp]
    rw [heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]
    have : (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hcoef j
    rw [this]
    simp

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNearRootOfUnityProductDecomposition

section

@[expose] public section

noncomputable section
open IsLocalRing UpperTheory.Et

private lemma mem_mm_top_iff {A D : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (x : D) :
    x ∈ mm (⊤ : Subalgebra A D) ↔ x ∈ (maximalIdeal A).map (algebraMap A D) := by
  simp [mm, Algebra.top_toSubmodule, Ideal.smul_top_eq_map]

private lemma mm_map {A E D : Type} [CommRing A] [IsLocalRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (B₀ : Subalgebra A E) (B : Subalgebra A D) (h : ∀ x ∈ B₀, ψ x ∈ B) {x : E}
    (hx : x ∈ mm B₀) : ψ x ∈ mm B := by
  unfold mm at hx ⊢
  exact Submodule.smul_induction_on (p := fun z => ψ z ∈ maximalIdeal A • Subalgebra.toSubmodule B) hx
    (fun r hr y hy => by
      rw [AlgHom.map_smul_of_tower]
      exact Submodule.smul_mem_smul hr (h y hy))
    (fun a b ha hb => by
      rw [map_add (f := _)]
      exact add_mem ha hb)

private lemma adjoin_map {A E D : Type} [CommRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (S : Set E) (B : Subalgebra A D) (h : ∀ x ∈ S, ψ x ∈ B) :
    ∀ x ∈ Algebra.adjoin A S, ψ x ∈ B := by
  intro x hx
  exact (Algebra.adjoin_le (S := B.comap ψ) h) hx

private lemma root_mem {S K : Type} [CommRing S] [Nontrivial S] [CommRing K] [IsDomain K] (f : S →+* K)
    (h : ∀ p : Polynomial S, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) (x : K) :
    ∀ (n : ℕ) (p : Polynomial S), p.Monic → p.natDegree = n → p.eval₂ f x = 0 → ∃ a : S, f a = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hdeg hx
    rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg] at hx
    simp at hx
  | succ n ih =>
    intro p hp hdeg hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr ha
    have hmX : (Polynomial.X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
    have hp' : ((Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a))).Monic := by
      rw [hfac]
      exact hp
    have hmq : (p /ₘ (Polynomial.X - Polynomial.C a)).Monic := hmX.of_mul_monic_left hp'
    have hdq : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree = n := by
      have := hmX.natDegree_mul hmq
      rw [hfac, hdeg, Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp [sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hmq hdq h1

private lemma unity_ratio {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (C : Subalgebra A D) (hC : Roots C) (q : ℕ) (hq : 0 < q) (a b : D) (h : a ^ q = b ^ q) :
    ∃ η ∈ C, η ^ q = 1 ∧ a = η * b := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨1, one_mem _, one_pow _, ?_⟩
    simp [zero_pow hq.ne', pow_eq_zero_iff hq.ne'] at h
    simp [h]
  · have hinj := IsFractionRing.injective D (FractionRing D)
    have hbK : algebraMap D (FractionRing D) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    have hbq : algebraMap D (FractionRing D) (b ^ q) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero q hb)
    obtain ⟨η, hη⟩ := root_mem ((algebraMap D (FractionRing D)).comp C.val.toRingHom) hC
      (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) q
      (Polynomial.X ^ q - Polynomial.C 1) (Polynomial.monic_X_pow_sub_C 1 hq.ne')
      (Polynomial.natDegree_X_pow_sub_C 1)
      (by simp [div_pow, ← map_pow, h, div_self hbq])
    have hη' : algebraMap D (FractionRing D) (η : D) = algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b := hη
    refine ⟨η, η.2, ?_, ?_⟩
    · apply hinj
      rw [map_pow, map_one, hη', div_pow, ← map_pow, ← map_pow, h, div_self hbq]
    · apply hinj
      rw [map_mul, hη', div_mul_cancel₀ _ hbK]

private lemma qth_root {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (S : Subalgebra A D) (hS : Roots S) (q : ℕ) (hq : 0 < q) (c : D) (hc : c ∈ S) :
    ∃ u ∈ S, u ^ q = c := by
  obtain ⟨a, ha⟩ := hS (Polynomial.X ^ q - Polynomial.C ⟨c, hc⟩) (Polynomial.monic_X_pow_sub_C _ hq.ne')
    (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hq)
  refine ⟨a, a.2, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ha
  have := congrArg Subtype.val (sub_eq_zero.mp ha)
  simpa using this

private lemma pow_root_mem {A : Type} [CommRing A] [IsLocalRing A] (P : Polynomial (LaurentPolynomial A))
    (q n : ℕ)
    (hP : ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) :
    (AdjoinRoot.root P ^ q - 1) ^ n ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
  have key : (AdjoinRoot.root P ^ q - 1) ^ n =
      -((P - (Polynomial.X ^ q - 1) ^ n).eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) := by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, AdjoinRoot.eval₂_root]
  rw [key, Polynomial.eval₂_eq_sum_range]
  refine neg_mem (sum_mem fun i _ => ?_)
  apply Ideal.mul_mem_right
  have hm := Ideal.mem_map_of_mem (AdjoinRoot.of P) (hP i)
  rwa [Ideal.map_map, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_eq] at hm

private theorem adjoinRoot_liftAlgHom_of_laurent {A D : Type} [CommRing A] [CommRing D] [Algebra A D]
    {P : Polynomial (LaurentPolynomial A)} (φ : LaurentPolynomial A →ₐ[A] D) (w : D)
    (h : Polynomial.eval₂ φ.toRingHom w P = 0) (z : LaurentPolynomial A) :
    AdjoinRoot.liftAlgHom P φ w h (AdjoinRoot.of P z) = φ z :=
  AdjoinRoot.liftAlgHom_of P φ w h z

theorem UpperTheory.exists_near_root_of_unity_product_decomposition :
    ∀ (A D : Type) [CommRing A] [HenselianLocalRing A] [CommRing D] [Algebra A D] [IsDomain D] (T : TC A D), T.Int → Roots T.B → Roots T.C → ∀ (q : ℕ), IsUnit (q : A) → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ u ∈ T.B, ∃ v ∈ T.C, u ^ q - 1 ∈ mm T.B ∧ v ^ q - 1 ∈ mm T.C ∧ w - u * v ∈ mm (⊤ : Subalgebra A D) := by
  intro A D _ _ _ _ _ T hInt hB hC q hq w hw
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      simp at hq
    · exact h0
  have hmono : ∀ (S : Subalgebra A D) (x : D), x ∈ mm S → x ∈ mm (⊤ : Subalgebra A D) :=
    fun S x hx => mm_map (AlgHom.id A D) S ⊤ (fun _ _ => Algebra.mem_top) hx
  obtain ⟨φ, P, n, hφt, hφs, hPm, hPw, hPc⟩ := UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity A D T hInt q hq0 w hw
  obtain ⟨kB, hkB⟩ := T.locB w
  obtain ⟨kC, hkC⟩ := T.locC w
  obtain ⟨k, hk, T', hFin, hCoord, ht', hs', hB', hC'⟩ := UpperTheory.exists_twoChart_adjoinRoot_laurent A P hPm (max kB kC)
  let ψ : AdjoinRoot P →ₐ[A] D := AdjoinRoot.liftAlgHom P φ w hPw
  have hψr : ψ (AdjoinRoot.root P) = w := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψt : ψ T'.t = T.t := by
    rw [ht']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφt
  have hψs : ψ T'.s = T.s := by
    rw [hs']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφs
  have hψB : ∀ x ∈ T'.B, ψ x ∈ T.B := by
    rw [hB']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψt]
      exact T.tB
    · rw [map_mul, map_pow, hψt, hψr]
      have e : T.t ^ k * w = T.t ^ (k - kB) * (T.t ^ kB * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_left _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.tB _) hkB
  have hψC : ∀ x ∈ T'.C, ψ x ∈ T.C := by
    rw [hC']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψs]
      exact T.sC
    · rw [map_mul, map_pow, hψs, hψr]
      have e : T.s ^ k * w = T.s ^ (k - kC) * (T.s ^ kC * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_right _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.sC _) hkC
  have hqS : IsUnit ((q : AdjoinRoot P ⧸ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))).comp
      (algebraMap A (AdjoinRoot P)))
    rwa [map_natCast] at this
  have hnil : IsNilpotent ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))
      (AdjoinRoot.root P)) ^ q - 1) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact pow_root_mem P q n hPc
  obtain ⟨y, hyq, hynil⟩ := (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqS).1 _ hnil
  obtain ⟨ω, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hω : ω ^ q - 1 ∈ mm (⊤ : Subalgebra A (AdjoinRoot P)) := by
    rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hyq, sub_self]
  obtain ⟨g', hg'B, g, hgC, μ, hg'1, hg1, hμ, hgg⟩ := UpperTheory.exists_factorization_near_root_of_unity_henselian A (AdjoinRoot P) T' hFin hCoord q hq ω hω
  have hG' : ψ g' ∈ T.B := hψB g' hg'B
  have hG : ψ g ∈ T.C := hψC g hgC
  have hG'1 : ψ g' - 1 ∈ mm T.B := by
    have := mm_map ψ T'.B T.B hψB hg'1
    rwa [map_sub, map_one] at this
  have hG1 : ψ g - 1 ∈ mm T.C := by
    have := mm_map ψ T'.C T.C hψC hg1
    rwa [map_sub, map_one] at this
  have hM : ψ μ - ψ ω ∈ mm (⊤ : Subalgebra A D) := by
    have := mm_map ψ ⊤ ⊤ (fun _ _ => Algebra.mem_top) hμ
    rwa [map_sub] at this
  have hGG : ψ g * ψ g' = (ψ μ) ^ q := by
    rw [← map_mul, hgg, map_pow]
  obtain ⟨u, hu, huq⟩ := qth_root T.B hB q hq0 (ψ g') hG'
  obtain ⟨v, hv, hvq⟩ := qth_root T.C hC q hq0 (ψ g) hG
  obtain ⟨η, hη, hηq, hηe⟩ := unity_ratio T.C hC q hq0 (ψ μ) (u * v)
    (by rw [mul_pow, huq, hvq, ← hGG, mul_comm])
  refine ⟨u, hu, η * v, mul_mem hη hv, ?_, ?_, ?_⟩
  · rw [huq]
    exact hG'1
  · rw [mul_pow, hηq, one_mul, hvq]
    exact hG1
  have hμe : u * (η * v) = ψ μ := by
    rw [hηe]
    ring
  rw [hμe]
  have hqD : IsUnit ((q : D ⧸ (maximalIdeal A).map (algebraMap A D))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D))).comp (algebraMap A D))
    rwa [map_natCast] at this
  have toQ : ∀ x : D, x ∈ mm (⊤ : Subalgebra A D) →
      Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) x = 0 := by
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← mem_mm_top_iff]
    exact hx
  rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqD).2
  · have := toQ _ hw
    rwa [map_sub, map_pow, map_one, sub_eq_zero] at this
  · have e1 := toQ _ (hmono _ _ hG1)
    have e2 := toQ _ (hmono _ _ hG'1)
    rw [map_sub, map_one, sub_eq_zero] at e1 e2
    rw [← map_pow, ← hGG, map_mul, e1, e2, one_mul]
  · obtain ⟨N, hN⟩ := hynil
    refine ⟨N, ?_⟩
    have h1 : (AdjoinRoot.root P - ω) ^ N ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub]
      exact hN
    have h2 : ψ ((AdjoinRoot.root P - ω) ^ N) ∈ (maximalIdeal A).map (algebraMap A D) := by
      have := Ideal.mem_map_of_mem (ψ : AdjoinRoot P →+* D) h1
      rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
    have h3 : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ μ) =
        Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ ω) := by
      rw [← sub_eq_zero, ← map_sub]
      exact toQ _ hM
    rw [h3, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← hψr, ← map_sub, ← map_pow]
    exact h2

end
end
end
