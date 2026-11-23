module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Invariant.Defs
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.FieldTheory.Fixed
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSeparableOfSumMem

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameResidue

theorem exists_sum_ne_zero {D k K : Type} [Group D] [Fintype D] [Field k] [Field K] [Algebra k K]
    (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0) : ∃ w : K, ∑ g, φ g w ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hf : Function.Injective (fun σ : K ≃ₐ[k] K => (σ : K →* K)) :=
    fun σ τ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x
  have hli := (linearIndependent_monoidHom K K).comp _ hf
  have hfib : ∀ σ ∈ Finset.univ.image φ,
      (Finset.univ.filter fun g => φ g = σ).card = Nat.card φ.ker := by
    intro σ hσ
    obtain ⟨g0, -, rfl⟩ := Finset.mem_image.1 hσ
    rw [MonoidHom.card_fiber_eq_of_mem_range φ ⟨g0, rfl⟩ ⟨1, rfl⟩, map_one,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])
  have hsum : ∀ w : K, ∑ g, φ g w = ∑ σ ∈ Finset.univ.image φ, (Nat.card φ.ker : K) * σ w := by
    intro w
    rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.image φ)
      (fun g _ => Finset.mem_image_of_mem φ (Finset.mem_univ g))]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
      hfib σ hσ, nsmul_eq_mul]
  refine h (linearIndependent_iff'.1 hli (Finset.univ.image φ) (fun _ => (Nat.card φ.ker : K)) ?_ (φ 1)
    (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))
  funext w
  have hw := hcon w
  rw [hsum w] at hw
  simpa [Finset.sum_apply] using hw

theorem finite_separable_of_sum_mem {D k K : Type} [Group D] [Fintype D] [Field k] [Field K]
    [Algebra k K] (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0)
    (hT : ∀ x : K, ∃ c : k, algebraMap k K c = ∑ g, φ g x) :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  classical
  obtain ⟨w, hw⟩ := exists_sum_ne_zero φ h
  obtain ⟨c, hc⟩ := hT w
  have hcw : algebraMap k K c ≠ 0 := by rw [hc]; exact hw
  have hfix : ∀ y : K, (∀ g : D, φ g y = y) → ∃ c' : k, algebraMap k K c' = y := by
    intro y hy
    obtain ⟨c', hc'⟩ := hT (y * w)
    refine ⟨c' / c, ?_⟩
    rw [map_div₀, hc', div_eq_iff hcw, hc]
    simp only [map_mul, hy, Finset.mul_sum]
  letI : MulSemiringAction D K := MulSemiringAction.compHom K φ
  have hF : ∀ x : FixedPoints.subfield D K, ∃ c' : k, algebraMap k K c' = x :=
    fun x => hfix x fun g => x.2 g
  refine ⟨?_, ?_⟩
  · let b := Module.finBasis (FixedPoints.subfield D K) K
    refine ⟨⟨Finset.univ.image b, eq_top_iff.2 fun x _ => ?_⟩⟩
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c', hc'⟩ := hF (b.repr x i)
    have he : b.repr x i • b i = c' • b i := by
      rw [Algebra.smul_def, Algebra.smul_def, hc']
      rfl
    rw [he]
    exact Submodule.smul_mem _ c' (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem b (Finset.mem_univ i))))
  · refine ⟨fun x => ?_⟩
    have hsF : (minpoly (FixedPoints.subfield D K) x).Separable :=
      Algebra.IsSeparable.isSeparable (FixedPoints.subfield D K) x
    have hl : (minpoly (FixedPoints.subfield D K) x).map
        (algebraMap (FixedPoints.subfield D K) K) ∈ Polynomial.lifts (algebraMap k K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨c', hc'⟩ := hF ((minpoly (FixedPoints.subfield D K) x).coeff n)
      exact ⟨c', hc'⟩
    obtain ⟨pk, hpk⟩ := Polynomial.mem_lifts _ |>.1 hl
    have hsep : pk.Separable := by
      rw [← Polynomial.separable_map (algebraMap k K), hpk, Polynomial.separable_map]
      exact hsF
    have hx : Polynomial.aeval x pk = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpk, Polynomial.eval_map,
        ← Polynomial.aeval_def, minpoly.aeval]
    exact hsep.of_dvd (minpoly.dvd k x hx)

theorem exists_not_mem_smul_mem {Γ B : Type} [Group Γ] [Finite Γ] [CommRing B]
    [MulSemiringAction Γ B] (q : Ideal B) [q.IsPrime] :
    ∃ y : B, y ∉ q ∧ ∀ g : Γ, g • q ≠ q → g • y ∈ q := by
  classical
  have hpow : ∀ h : Γ, h ^ (Nat.card Γ - 1) = h⁻¹ := fun h =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])
  have hex : ∀ g : Γ, ∃ a : B, a ∉ q ∧ (g • q ≠ q → g • a ∈ q) := by
    intro g
    by_cases hg : g • q = q
    · exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top inferInstance),
        fun h => absurd hg h⟩
    · by_contra hcon
      apply hg
      have h1 : ∀ a : B, g • a ∈ q → a ∈ q := fun a ha =>
        by_contra fun hn => hcon ⟨a, hn, fun _ => ha⟩
      have h2 : ∀ x ∈ q, g⁻¹ • x ∈ q := fun x hx => h1 _ (by rwa [smul_inv_smul])
      have h3 : ∀ m : ℕ, ∀ x ∈ q, (g⁻¹) ^ m • x ∈ q := by
        intro m
        induction m with
        | zero => intro x hx; rwa [pow_zero, one_smul]
        | succ m ih => intro x hx; rw [pow_succ', mul_smul]; exact h2 _ (ih x hx)
      have h5 : ∀ x ∈ q, g • x ∈ q := fun x hx => by
        have := h3 (Nat.card Γ - 1) x hx
        rwa [hpow, inv_inv] at this
      apply Ideal.ext
      intro x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact ⟨fun hx => by simpa using h5 _ hx, h2 x⟩
  choose a ha using hex
  haveI := Fintype.ofFinite Γ
  refine ⟨∏ g, a g, ?_, fun g hg => ?_⟩
  · exact prod_mem (S := q.primeCompl) fun g _ => (ha g).1
  · rw [Finset.smul_prod']
    exact q.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => g • a i) (Finset.mem_univ g)) ((ha g).2 hg)

theorem residue_finite_separable : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction Γ B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ] (q : Ideal B) [q.IsPrime] (k K : Type) [Field k] [Field K] [Algebra (A ⧸ q.under A) k] [IsFractionRing (A ⧸ q.under A) k] [Algebra (B ⧸ q) K] [IsFractionRing (B ⧸ q) K] [Algebra k K], (∀ a : A, algebraMap k K (algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a)) = algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (algebraMap A B a))) → (Nat.card (q.inertia Γ) : B) ∉ q → FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  intro Γ _ _ A B _ _ _ _ _ _ q _ k K _ _ _ _ _ _ _ hcomp hin
  classical
  haveI := Fintype.ofFinite Γ
  letI : Algebra (A ⧸ q.under A) K :=
    ((algebraMap k K).comp (algebraMap (A ⧸ q.under A) k)).toAlgebra
  haveI : IsScalarTower (A ⧸ q.under A) k K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A ⧸ q.under A) (B ⧸ q) K := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hcomp a
  let ψ := Ideal.Quotient.stabilizerHom q (q.under A) Γ
  let φ : MulAction.stabilizer Γ q →* (K ≃ₐ[k] K) :=
    (IsFractionRing.fieldEquivOfAlgEquivHom k K).comp ψ
  have hφ : ∀ (g : MulAction.stabilizer Γ q) (u : B ⧸ q),
      φ g (algebraMap (B ⧸ q) K u) = algebraMap (B ⧸ q) K (ψ g u) := fun g u => by
    simp [φ, IsFractionRing.fieldEquivOfAlgEquivHom, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  have hψ : ∀ (g : MulAction.stabilizer Γ q) (b : B),
      ψ g (Ideal.Quotient.mk q b) = Ideal.Quotient.mk q ((g : Γ) • b) := fun g b => by
    first
      | rfl
      | simp [ψ, Ideal.Quotient.stabilizerHom]
  have hι : ∀ u : B ⧸ q, u ≠ 0 → algebraMap (B ⧸ q) K u ≠ 0 := fun u hu h0 =>
    hu (IsFractionRing.injective (B ⧸ q) K (h0.trans (map_zero _).symm))
  have hsplit : ∀ F : Γ → K, (∀ g : Γ, g ∉ MulAction.stabilizer Γ q → F g = 0) →
      ∑ g, F g = ∑ g : MulAction.stabilizer Γ q, F g := by
    intro F hF
    have hs := Finset.sum_subset (Finset.subset_univ
      (Finset.univ.map (Function.Embedding.subtype (· ∈ MulAction.stabilizer Γ q)))) (f := F)
      (fun g _ hg => hF g fun hs => hg (Finset.mem_map.2 ⟨⟨g, hs⟩, Finset.mem_univ _, rfl⟩))
    rw [← hs, Finset.sum_map]
    rfl
  have hle : q.inertia Γ ≤ MulAction.stabilizer Γ q := by
    intro g hg
    have hg' : g⁻¹ ∈ q.inertia Γ := inv_mem hg
    rw [MulAction.mem_stabilizer_iff]
    apply Ideal.ext
    intro x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hx : g⁻¹ • x - x ∈ q := hg' x
    constructor
    · intro h1; simpa using q.sub_mem h1 hx
    · intro h1; simpa using q.add_mem hx h1
  have hmem : ∀ g : MulAction.stabilizer Γ q, g ∈ φ.ker ↔ (g : Γ) ∈ q.inertia Γ := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      have := congrArg (fun e : K ≃ₐ[k] K => e (algebraMap (B ⧸ q) K (Ideal.Quotient.mk q x))) h
      simp only [hφ, hψ, AlgEquiv.one_apply] at this
      exact Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ q) K this)
    · intro h
      ext z
      obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
      simp only [map_div₀, hφ, hψ, AlgEquiv.one_apply]
      rw [Ideal.Quotient.eq.2 (h u), Ideal.Quotient.eq.2 (h v)]
  have hcardeq : Nat.card φ.ker = Nat.card (q.inertia Γ) :=
    Nat.card_congr
      { toFun := fun g => ⟨((g.1 : MulAction.stabilizer Γ q) : Γ), (hmem g.1).1 g.2⟩
        invFun := fun h => ⟨⟨h.1, hle h.2⟩, (hmem ⟨h.1, hle h.2⟩).2 h.2⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
  have hkerK : ((Nat.card φ.ker : ℕ) : K) ≠ 0 := by
    rw [hcardeq]
    intro h0
    apply hin
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (B ⧸ q) K
    simpa using h0
  obtain ⟨y, hyq, hy⟩ := exists_not_mem_smul_mem (Γ := Γ) q
  have hB : ∀ u : B ⧸ q, ∃ c : k, algebraMap k K c =
      ∑ g, φ g (algebraMap (B ⧸ q) K u * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y)) := by
    intro u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • (b * y))
      (fun h => by
        rw [Finset.smul_sum]
        exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [mul_smul]))
    refine ⟨algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a), ?_⟩

    rw [hcomp, ha, map_sum, map_sum]
    simp only [← map_mul, hφ, hψ]
    refine hsplit (fun g => algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y)))) (fun g hg => ?_)
    have hne : g • q ≠ q := fun h => hg (MulAction.mem_stabilizer_iff.2 h)
    show algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y))) = 0
    rw [smul_mul', Ideal.Quotient.eq_zero_iff_mem.2 (q.mul_mem_left _ (hy g hne)), map_zero]
  have hTinv : ∀ (x : K) (h : MulAction.stabilizer Γ q), φ h (∑ g, φ g x) = ∑ g, φ g x := by
    intro x h

    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
  have hTlin : ∀ z x : K, (∀ g, φ g z = z) → ∑ g, φ g (z * x) = z * ∑ g, φ g x := by
    intro z x hz
    simp only [map_mul, hz, Finset.mul_sum]
  obtain ⟨w0, hw0⟩ := exists_sum_ne_zero φ hkerK
  have hyq' : algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) ≠ 0 :=
    hι _ (fun h0 => hyq (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  have hfixk : ∀ z : K, (∀ g, φ g z = z) → ∃ c : k, algebraMap k K c = z := by
    intro z hz
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
    have hv0 : algebraMap (B ⧸ q) K v ≠ 0 := hι _ (nonZeroDivisors.ne_zero hv)
    set c0 := algebraMap (B ⧸ q) K v * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) with hc0def
    have hc0 : c0 ≠ 0 := mul_ne_zero hv0 hyq'
    have ht : ∃ t : B ⧸ q, ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hw0
      obtain ⟨t1, t2, ht2, hdiv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) (w0 / c0)
      have ht20 : t2 ≠ 0 := nonZeroDivisors.ne_zero ht2
      set M' := ∏ g ∈ Finset.univ.erase (1 : MulAction.stabilizer Γ q), ψ g t2 with hM'
      have hM : ∏ g, ψ g t2 = t2 * M' := by
        rw [← Finset.mul_prod_erase Finset.univ (fun g => ψ g t2) (Finset.mem_univ 1), map_one]
        rfl
      have hMinv : ∀ h, φ h (algebraMap (B ⧸ q) K (∏ g, ψ g t2)) =
          algebraMap (B ⧸ q) K (∏ g, ψ g t2) := by
        intro h
        rw [hφ, map_prod]
        congr 1
        exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
      have hM0 : ∏ g, ψ g t2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun g _ h0 =>
        ht20 ((ψ g).injective (h0.trans (map_zero _).symm))
      have hdiv' : algebraMap (B ⧸ q) K t1 * c0 = w0 * algebraMap (B ⧸ q) K t2 := by
        rw [div_eq_div_iff (hι _ ht20) hc0] at hdiv
        exact hdiv
      have hw : w0 * algebraMap (B ⧸ q) K (∏ g, ψ g t2) = c0 * algebraMap (B ⧸ q) K (t1 * M') := by
        rw [hM, map_mul, map_mul]
        linear_combination (-(algebraMap (B ⧸ q) K M')) * hdiv'
      have h1 : algebraMap (B ⧸ q) K (∏ g, ψ g t2) * ∑ g, φ g w0 = 0 := by
        rw [← hTlin _ w0 hMinv, mul_comm, hw]
        exact hcon _
      exact (mul_eq_zero.1 h1).resolve_left (hι _ hM0)
    obtain ⟨t, ht⟩ := ht
    obtain ⟨c1, hc1⟩ := hB (u * t)
    obtain ⟨c2, hc2⟩ := hB (v * t)
    refine ⟨c1 / c2, ?_⟩
    have e2 : ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) = algebraMap k K c2 := by
      rw [hc2, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def]
      ring
    have e1 : ∑ g, φ g (z * (c0 * algebraMap (B ⧸ q) K t)) = algebraMap k K c1 := by
      rw [hc1, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def, ← huv, div_mul_eq_mul_div, div_eq_iff hv0]
      ring
    rw [hTlin z _ hz, e2] at e1
    have hc2ne : algebraMap k K c2 ≠ 0 := by rw [← e2]; exact ht
    rw [map_div₀, ← e1, mul_div_assoc, div_self hc2ne, _root_.mul_one]
  exact finite_separable_of_sum_mem φ hkerK (fun x => hfixk _ (hTinv x))

end GlobalTheory.TameResidue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueFieldMapFiniteSeparableOfTame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_eq_evaluation_div {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (z : X.residueField x) : ∃ a b : Γ(X, U), z = X.evaluation U x hx a / X.evaluation U x hx b := by
  classical
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have he : ∀ c, X.evaluation U x hx c =
      (X.residue x).hom (algebraMap Γ(X, U) (X.presheaf.stalk x) c) := fun c => rfl
  obtain ⟨s, rfl⟩ : ∃ s, (X.residue x).hom s = z := IsLocalRing.residue_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  change s * algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U)) =
    algebraMap Γ(X, U) (X.presheaf.stalk x) a at hab
  have hb0 : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U))) :=
    IsLocalization.map_units _ b
  have hb := hb0.map (X.residue x).hom
  refine ⟨a, b, ?_⟩
  rw [he, he, eq_div_iff hb.ne_zero, ← map_mul (X.residue x).hom, hab]

theorem isFractionRing_residueField {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : Ideal Γ(X, U)) (hq : ∀ a, a ∈ q ↔ X.evaluation U x hx a = 0) :
    letI := (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
    IsFractionRing (Γ(X, U) ⧸ q) (X.residueField x) := by
  letI : Algebra (Γ(X, U) ⧸ q) (X.residueField x) :=
    (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
  have hmk : ∀ a, algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a) =
      X.evaluation U x hx a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hmk] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq a).2 hc)
  haveI : NoZeroDivisors (Γ(X, U) ⧸ q) :=
    hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    haveI : Nontrivial (Γ(X, U) ⧸ q) :=
      ⟨⟨0, 1, fun h => by simpa using congrArg (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) h⟩⟩
    exact nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨a, b, hz⟩ := exists_eq_evaluation_div hU x hx z
    by_cases hb : X.evaluation U x hx b = 0
    · refine ⟨(0, 1), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 1 =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 0
      rw [hz, hb, div_zero, zero_mul, map_zero]
    · have hb' : Ideal.Quotient.mk q b ≠ 0 := by
        intro h
        apply hb
        rw [← hmk, h, map_zero]
      refine ⟨(Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q b, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q b) =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a)
      rw [hz, hmk, hmk, div_mul_cancel₀ _ hb]
  · intro c d h
    exact ⟨1, by rw [hinj h]⟩

theorem residueFieldMap_finite_separable_of_tame {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0)
    (x : X) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (X'.residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable (X'.residueField (π x)) (X.residueField x) := by
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hx : π x ∈ W := hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : Γ) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let ev := X.evaluation (π ⁻¹ᵁ W) x hx
  let q : Ideal Γ(X, π ⁻¹ᵁ W) := RingHom.ker ev.hom
  have : q.IsPrime := RingHom.ker_isPrime _
  have hq : ∀ a, a ∈ q ↔ ev a = 0 := fun a ↦ Iff.rfl
  have hnat (a : Γ(X', W)) : π.residueFieldMap x (X'.evaluation W (π x) hx a) = ev (π.app W a) :=
    Scheme.evaluation_naturality_apply π x hx a
  have hp : ∀ a, a ∈ q.under Γ(X', W) ↔ X'.evaluation W (π x) hx a = 0 := fun a ↦ by
    rw [← map_eq_zero_iff _ (π.residueFieldMap x).hom.injective, hnat]
    rfl
  let := (Ideal.Quotient.lift q ev.hom fun a ha ↦ (hq a).1 ha).toAlgebra
  let := (Ideal.Quotient.lift _ (X'.evaluation W (π x) hx).hom fun a ha ↦ (hp a).1 ha).toAlgebra
  have := isFractionRing_residueField hU x hx q hq
  have := isFractionRing_residueField hW (π x) hx _ hp
  refine TameResidue.residue_finite_separable Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) q _ _ hnat fun hc ↦ ?_
  let Ω := AlgebraicClosure (X.residueField x)
  let jΩ : X.residueField x ⟶ CommRingCat.of Ω := CommRingCat.ofHom (algebraMap (X.residueField x) Ω)
  let y : Sp Ω ⟶ X := Spec.map (ev ≫ jΩ) ≫ hU.fromSpec
  have key (g : Γ) : g⁻¹ ∈ q.inertia Γ ↔ y ≫ (ρ g).asIso.hom = y := by
    have e : y ≫ (ρ g).asIso.hom = Spec.map ((ρ g).asIso.hom.appLE _ _ (hst g) ≫ ev ≫ jΩ) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
    have : Mono jΩ := ConcreteCategory.mono_of_injective _ jΩ.hom.injective
    rw [e, cancel_mono, Spec.map_inj, ← Category.assoc, cancel_mono]
    have e₂ (s) : g⁻¹ • s = (ρ g).asIso.hom.appLE _ _ (hst g) s := by
      change (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = _
      simp only [inv_inv]
    refine Iff.trans AddSubgroup.mem_inertia ⟨fun h ↦ ?_, fun h s ↦ ?_⟩
    · ext s
      have := (hq _).1 (h s)
      rw [map_sub, sub_eq_zero, e₂] at this
      exact this
    · refine (hq _).2 ?_
      rw [map_sub, sub_eq_zero, e₂]
      exact congr($h s)
  have hcard : Nat.card {g // y ≫ (ρ g).asIso.hom = y} = Nat.card (q.inertia Γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ (key g).symm.trans (inv_mem_iff (H := q.inertia Γ)))
  apply ht Ω y
  rw [hcard]
  have := congrArg jΩ.hom ((hq _).1 hc)
  simpa using this

theorem splitFibres_descend_of_tame_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G.left ⟶ G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → IsGrpPullback G G' π φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro Γ _ _ X X' ρ π G _ G' _ φ hq ht hφ hS x'
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  obtain ⟨_, hπ, hV⟩ := hq
  obtain ⟨x, rfl⟩ := π.surjective x'
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨h₁, h₂⟩ := residueFieldMap_finite_separable_of_tame ρ π hπ
    (fun W _ s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2) ht x
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let : Algebra (X'.residueField (π x)) k :=
    ((algebraMap (X.residueField x) k).comp (π.residueFieldMap x).hom).toAlgebra
  have : IsScalarTower (X'.residueField (π x)) (X.residueField x) k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨k, inferInstance, inferInstance, Module.Finite.trans (X.residueField x) k,
    Algebra.IsSeparable.trans _ (X.residueField x) k, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField (π x)) k)) ≫ X'.fromSpecResidueField (π x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    rfl
  rw [← key]
  generalize Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x = t at hGt
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' π)
  have : IsMonHom ((Over.pullback t).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₃ := isGt_of_iso ((Over.pullback t).mapIso e) hGt
  have : IsMonHom (pullCompIso t π G').symm.hom := inferInstanceAs (IsMonHom (pullCompIso t π G').inv)
  exact isGt_of_iso (pullCompIso t π G').symm h₃

end GlobalTheory
end
end
