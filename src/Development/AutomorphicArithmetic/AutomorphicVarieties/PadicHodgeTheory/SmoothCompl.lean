module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfHomogeneousAevalMemMaximalIdealPowSucc
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Localization.Integer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsHomogeneousLiftModKerPowSuccSup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNotMemMulMemIdealOfForallPrimePowSup
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nakayama
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PowerSeriesApproximationModMaximal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimEqHeightKerSectionAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimMvPowerSeriesFinField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothComplA
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDerivationsDualToCotangentParameters

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.exists_derivations_dual_to_cotangent_parameters :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → ∃ (n : ℕ) (D : Fin n → (R →ₗ[O] E)) (t : Fin n → R) (c : O), c ≠ 0 ∧ (∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) ∧ (∀ i, ∀ a ∈ I, D i a = 0) ∧ (∀ i, x (t i) = 0) ∧ (∀ i j, D j (t i) = if j = i then algebraMap O E c else 0) ∧ ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I := by
  intro O E _ _ _ _ _ R _ _ _ I x hI
  classical
  set p : Ideal R := RingHom.ker x with hp
  have hmem : ∀ a, a ∈ p ↔ x a = 0 := fun a => RingHom.mem_ker
  let J : Ideal R := p ^ 2 ⊔ I
  have hJp : J ≤ p := sup_le (Ideal.pow_le_self two_ne_zero) hI
  let N : Submodule O R := Submodule.span O {(1 : R)} ⊔ J.restrictScalars O
  let f : (R ⧸ N) →ₗ[O] TensorProduct O E (R ⧸ N) := TensorProduct.mk O E (R ⧸ N) 1
  let π : R →ₗ[O] TensorProduct O E (R ⧸ N) := f ∘ₗ N.mkQ
  have hπN : ∀ a ∈ N, π a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero N).2 ha
    simp only [π, LinearMap.comp_apply, this, map_zero]
  have hJN : ∀ a ∈ J, a ∈ N := fun a ha => Submodule.mem_sup_right (by simpa using ha)
  have h1N : (1 : R) ∈ N := Submodule.mem_sup_left (Submodule.subset_span rfl)
  have hsub : ∀ a : R, a - x a • (1 : R) ∈ p := by
    intro a
    rw [hmem]
    simp
  have hder : ∀ a b, π (a * b) = x a • π b + x b • π a := by
    intro a b
    have h1 : (a - x a • (1 : R)) * (b - x b • (1 : R)) ∈ N := by
      apply hJN
      apply Submodule.mem_sup_left
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    have h2 : a * b = (a - x a • (1 : R)) * (b - x b • (1 : R)) - (x a * x b) • (1 : R)
        + (x a • b + x b • a) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [h2, map_add (f := _), hπN _ (N.sub_mem h1 (N.smul_mem _ h1N))]
    simp
  have hker : ∀ a, x a = 0 → π a = 0 → ∃ e : O, e ≠ 0 ∧ e • a ∈ J := by
    intro a ha h
    have h' : f (N.mkQ a) = 0 := h
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) f).1 h'
    refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    have h3 : (s : O) • a ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N]
      simpa [Submonoid.smul_def] using hs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hv' : v ∈ J := by simpa using hv
    have hxv : x v = 0 := (hmem v).1 (hJp hv')
    have := congrArg x huv
    simp [hxv, ha] at this
    rw [← huv, this]
    simpa using hv'
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian p)
  have hgp : ∀ i, x (g i) = 0 := fun i => (hmem _).1 (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range (π ∘ g)) = ⊤ := by
    have key : ∀ a ∈ p, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a ha
      rw [← hg] at ha
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha

      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_mul, hder, hgp, zero_smul, add_zero, ← IsScalarTower.algebraMap_smul E]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have key2 : ∀ a, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a
      have := key _ (hsub a)
      rwa [map_sub, hπN _ (N.smul_mem _ h1N), sub_zero] at this
    rw [eq_top_iff]
    rintro v -
    induction v with
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | tmul e q =>
      obtain ⟨a, rfl⟩ := N.mkQ_surjective q
      have : e ⊗ₜ[O] N.mkQ a = e • π a := by
        simp [π, f, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key2 a)
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' E (π ∘ g)
  haveI : Finite κ := Finite.of_injective a hainj
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ E (TensorProduct O E (R ⧸ N)) :=
    Module.Basis.mk hli (by rw [hsp, hspan])
  let b := b0.reindex ε
  let t : Fin n → R := fun i => g (a (ε.symm i))
  have hbt : ∀ i, π (t i) = b i := by
    intro i
    simp [b, b0, t]
  refine ⟨n, fun i => ((b.coord i).restrictScalars O) ∘ₗ π, t, 1, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro i u v
    rw [LinearMap.comp_apply, hder, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    rfl
  · intro i u hu
    simp [hπN u (hJN u (Submodule.mem_sup_right hu))]
  · intro i
    exact hgp _
  · intro i j
    simp [hbt, Finsupp.single_apply, eq_comm]
  · intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun i => b.repr (π u) i)
    choose o ho using hd
    have h0 : π ((d : O) • u - ∑ i, o i • t i) = 0 := by

      rw [map_sub, map_smul, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (π u), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbt, ← IsScalarTower.algebraMap_smul E (o i), ho, smul_assoc]
    obtain ⟨e, he, hJ⟩ := hker _ (by simp [hu, t, hgp]) h0
    refine ⟨e * d, fun i => e * o i, mul_ne_zero he (nonZeroDivisors.coe_ne_zero d), ?_⟩
    simpa [smul_sub, Finset.smul_sum, mul_smul] using hJ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HeightKerSectionLeOfCotangentGenerators

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.height_ker_section_le_of_cotangent_generators :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (t : Fin n → S), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2) → (RingHom.ker x).height ≤ (n : ℕ∞) := by
  classical
  intro O S _ _ _ _ _ x n t ht hx
  set P := RingHom.ker x with hPdef
  haveI hP : P.IsPrime := RingHom.ker_isPrime x
  set L := Localization.AtPrime P
  set T : Ideal L := Ideal.span ((Finset.univ.image (fun i => algebraMap S L (t i)) : Finset L) : Set L) with hT
  have hTm : T ≤ maximalIdeal L := by
    rw [hT, Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (ht i)
  have key : Ideal.map (algebraMap S L) P ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨e, o, he, hmem⟩ := hx a ha
    have hunit : IsUnit (algebraMap S L (algebraMap O S e)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L P]
      intro hin
      apply he
      have : x (algebraMap O S e) = 0 := hin
      simpa using this
    rw [Ideal.mem_comap]
    have h2 : algebraMap S L (e • a - ∑ i, o i • t i) ∈ maximalIdeal L • maximalIdeal L := by
      rw [smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul, ← pow_two]
      exact Ideal.mem_map_of_mem _ hmem
    have h3 : algebraMap S L (∑ i, o i • t i) ∈ T := by

      rw [map_sum]
      refine Ideal.sum_mem _ (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      simp
    have h4 : algebraMap S L (algebraMap O S e) * algebraMap S L a ∈ T ⊔ maximalIdeal L • maximalIdeal L := by
      have : algebraMap S L (algebraMap O S e) * algebraMap S L a = algebraMap S L (∑ i, o i • t i) + algebraMap S L (e • a - ∑ i, o i • t i) := by
        rw [← map_mul, ← Algebra.smul_def, ← map_add (f := _)]
        congr 1
        abel
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right h2)
    obtain ⟨u, hu⟩ := hunit
    have : algebraMap S L a = ((u⁻¹ : Lˣ) : L) * (algebraMap S L (algebraMap O S e) * algebraMap S L a) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h4
  have hmT : maximalIdeal L ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at key
  have hmle : maximalIdeal L ≤ T :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hmT
  have heq : T = maximalIdeal L := le_antisymm hTm hmle
  have hmin : maximalIdeal L ∈ T.minimalPrimes := by
    rw [heq]
    exact ⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hPL : P.height = (maximalIdeal L).height := by
    rw [← IsLocalization.height_under P.primeCompl (maximalIdeal L), Localization.AtPrime.under_maximalIdeal]
  rw [hPL]
  refine hh.trans ?_
  have hc : (Finset.univ.image (fun i => algebraMap S L (t i))).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => algebraMap S L (t i)))
  exact_mod_cast hc
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem sc_pi (E : Type) [Field E] (n k : ℕ) :
    ∃ π : (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (k + 2)) →ₐ[E] E,
      (∀ g, π (Ideal.Quotient.mk _ g) = MvPowerSeries.constantCoeff g) ∧ ∀ a, π a = 0 → IsNilpotent a := by
  let cc : MvPowerSeries (Fin n) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) E →+* E) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  refine ⟨Ideal.Quotient.liftₐ _ cc fun g hg => (sc_max E n g).1 (Ideal.pow_le_self (by omega) hg),
    fun g => rfl, fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨k + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ((sc_max E n g).2 ha) _

private theorem sc_inj {O E R : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E)
    (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I)
    (N : ℕ) : ∀ a, φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N →
      ∃ e : O, e ≠ 0 ∧ e • a ∈ RingHom.ker x ^ N ⊔ I := by
  have hmap : ∀ k, ∀ b ∈ RingHom.ker x ^ k ⊔ I, φ b ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k := by
    intro k
    have : RingHom.ker x ^ k ⊔ I ≤ (maximalIdeal (MvPowerSeries (Fin n) E) ^ k).comap (φ : R →+* _) := by
      refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) k) (Ideal.le_comap_pow _ k)) fun y hy => ?_
      · refine (sc_max E n (φ y)).2 ?_
        rw [hconst, show x y = 0 from hy, map_zero]
      · show φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k
        rw [show φ y = 0 from hI hy]
        exact zero_mem _
    exact fun b hb => this hb
  induction N with
  | zero => exact fun a _ => ⟨1, one_ne_zero, by simp⟩
  | succ N ih =>
    intro a ha
    obtain ⟨e, he, h1⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ N) ha)
    obtain ⟨b, hb, i, hi, hbi⟩ := Submodule.mem_sup.1 h1
    obtain ⟨e', h, he', hh, h2⟩ := UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup O R I x n t ht0 hspan N b hb
    have hφb : φ b = e • φ a := by
      rw [← map_smul, ← hbi, map_add (f := _), show φ i = 0 from hI hi, add_zero]
    have h3 : MvPolynomial.aeval (fun j => φ (t j)) h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) := by
      have h4 := hmap _ _ h2
      rw [map_sub, map_smul, hφb, MvPolynomial.comp_aeval_apply] at h4
      have h5 : e' • e • φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) :=
        Submodule.smul_of_tower_mem _ _ (Submodule.smul_of_tower_mem _ _ ha)
      simpa using sub_mem h5 h4
    have h0 := UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ O E n _ c hc ht N h hh h3
    rw [h0, map_zero, sub_zero] at h2
    refine ⟨e' * e, mul_ne_zero he' he, ?_⟩
    rw [mul_smul, ← hbi, smul_add]
    exact add_mem h2 (Ideal.mem_sup_right (Submodule.smul_of_tower_mem _ _ hi))

private theorem sc_dim {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ringKrullDim (R ⧸ RingHom.ker φ) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have : IsCO O (R ⧸ RingHom.ker φ) :=
    co_quot O R _ (Ideal.Quotient.mkₐ O _) Ideal.Quotient.mk_surjective
  have hPx : ∀ a ∈ RingHom.ker φ, x a = 0 := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨x', hx'⟩ : ∃ x' : (R ⧸ RingHom.ker φ) →ₐ[O] O, ∀ a, x' (Ideal.Quotient.mk _ a) = x a :=
    ⟨Ideal.Quotient.liftₐ _ x hPx, fun _ => rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : (R ⧸ RingHom.ker φ) →ₐ[O] MvPowerSeries (Fin n) E,
      ∀ a, φ' (Ideal.Quotient.mk _ a) = φ a := ⟨Ideal.Quotient.liftₐ _ φ fun _ h => h, fun _ => rfl⟩
  have h1 := UpperTheory.ringKrullDim_mvPowerSeries_fin_field O E _ x' n φ' (fun i => Ideal.Quotient.mk _ (t i)) c hc
    (fun a => by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hφ', hx', hconst])
    (fun i => by rw [hφ']; exact ht i)
  have h2 := UpperTheory.height_ker_section_le_of_cotangent_generators O _ x' n (fun i => Ideal.Quotient.mk _ (t i)) (fun i => by rw [hx', ht0])
    (fun a ha => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨e, o, he, h⟩ := hspan a (by rw [← hx', ha])
      refine ⟨e, o, he, ?_⟩
      have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker x' ^ 2).comap (Ideal.Quotient.mk (RingHom.ker φ)) := by
        refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)) fun y hy => ?_
        · exact (hx' y).trans hy
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (hI hy)]
          exact zero_mem _
      have h3 : Ideal.Quotient.mkₐ O (RingHom.ker φ) (e • a - ∑ i, o i • t i) ∈ RingHom.ker x' ^ 2 := hle h

      simpa only [map_sub, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using h3)
  rw [UpperTheory.ringKrullDim_eq_height_ker_section_add_one O _ x', le_antisymm h2 h1]
  norm_cast

private theorem sc_end {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (hIx : I ≤ RingHom.ker x) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ∃ P : Ideal R, UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧
      (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧
      ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hinj := sc_inj I x n φ t c hc hI hconst ht0 ht hspan
  have hPx : RingHom.ker φ ≤ RingHom.ker x := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨y, hy, hyP⟩ := UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup R I (RingHom.ker x) (RingHom.ker φ) (RingHom.ker_isPrime _) hIx
    fun a ha N => by
      obtain ⟨e, he, h⟩ := hinj N a (by rw [show φ a = 0 from ha]; exact zero_mem _)
      refine ⟨algebraMap O R e, fun h' => he ?_, by rwa [← Algebra.smul_def]⟩
      simpa using h'
  have hle : ∀ Q : Ideal R, Q.IsPrime → I.radical ≤ Q → Q ≤ RingHom.ker x → RingHom.ker φ ≤ Q :=
    fun Q hQ h1 h2 a ha => (hQ.mem_or_mem (h1 (Ideal.le_radical (hyP a ha)))).resolve_left fun h => hy (h2 h)
  have hrad : I.radical ≤ RingHom.ker φ := hP.radical_le_iff.2 hI
  refine ⟨RingHom.ker φ, ⟨rfl, hconst, UpperTheory.power_series_approximation_mod_maximal O E R n φ t c hc ht, fun N a ha => ?_⟩, hI, ⟨y, hy, hyP⟩,
    fun Q hQ => ⟨fun h => ?_, fun h => h ▸ hPx⟩, ⟨⟨hP, hrad⟩, fun Q hQ h => hle Q hQ.1 hQ.2 (h.trans hPx)⟩,
    sc_dim I x n φ t c hc hI hconst ht0 ht hspan⟩
  · obtain ⟨e, he, h⟩ := hinj N a ha
    exact ⟨e, he, sup_le_sup_left hI _ h⟩
  · have h1 := hle Q hQ.1.1 hQ.1.2 h
    exact le_antisymm (hQ.2 ⟨hP, hrad⟩ h1) h1

theorem UpperTheory.V.Loc.smoothCompl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ f' : R →ₐ[O] B', I ≤ RingHom.ker f' → (∀ a, π' (f' a) = algebraMap O E (x a)) → ∃ f : R →ₐ[O] B, I ≤ RingHom.ker f ∧ ∀ a, p (f a) = f' a) → ∃ (n : ℕ) (P : Ideal R) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧ (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧ ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ R _ _ _ I x hIx H
  obtain ⟨n, D, t, c, hc, hD, hDI, ht0, htD, hspan⟩ := UpperTheory.exists_derivations_dual_to_cotangent_parameters O E R I x hIx
  obtain ⟨f₀, hf₀⟩ := sc_first x n D hD
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) E)) (MvPowerSeries (Fin n) E) := by
    rw [← sc_span]; infer_instance
  have hfin : ∀ k, Module.Finite ℚ_[l] (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
    fun k => by
      have : Module.Finite E (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
        GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le (N := k) (by rw [sc_span])
      exact Module.Finite.trans E _
  have hc0 : ∀ a g, Ideal.Quotient.mk _ g = f₀ a → MvPowerSeries.constantCoeff g = algebraMap O E (x a) := by
    intro a g hg
    rw [hf₀, Ideal.Quotient.eq] at hg
    have := (sc_max E n _).1 (Ideal.pow_le_self (by omega) hg)
    simpa [sub_eq_zero] using this
  obtain ⟨φ, hφI, hφ⟩ := sc_tower (maximalIdeal (MvPowerSeries (Fin n) E)) I f₀
    (fun a ha => by
      rw [RingHom.mem_ker, hf₀, show x a = 0 from hIx ha]
      simp [hDI _ a ha])
    (fun N f' h1 h2 => by
      obtain ⟨π, hπ, hn⟩ := sc_pi E n (N + 1)
      obtain ⟨π', hπ', hn'⟩ := sc_pi E n N
      have := hfin (N + 1 + 2)
      have := hfin (N + 2)
      refine H _ π hn _ π' hn' (Ideal.Quotient.factorₐ E (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)))
        (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2))) (AlgHom.ext fun b => ?_) f' h1 fun a => ?_
      · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (hπ' g).trans (hπ g).symm
      · obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f' a)
        rw [← hg, hπ']
        refine hc0 a g ?_
        rw [← h2, ← hg, Ideal.Quotient.factor_mk])
  obtain ⟨P, hP⟩ := sc_end I x hIx n φ t c hc hφI (fun a => hc0 a _ (hφ a)) ht0 (fun i => by
    have h := hφ (t i)
    rw [hf₀, Ideal.Quotient.eq] at h
    simpa [ht0, htD, apply_ite, Algebra.smul_def, MvPowerSeries.algebraMap_apply] using h) hspan
  exact ⟨n, P, φ, hP⟩
end
end
