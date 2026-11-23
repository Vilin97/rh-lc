module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeffStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSecNormCoeffLocalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosedStatement
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReversedCharpolyCoeffNotMemPrime

section

@[expose] public section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  set K := FractionRing A
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed (K := K) φ hφ b
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (charK φ hφ K b).natDegree = P.natDegree := by
    rw [← hP]; exact natDegree_map_eq_of_injective hinj P
  have hmon : P.Monic := by
    have h1 := charK_monic φ hφ K b
    rw [← hP] at h1
    apply hinj
    rw [Monic, leadingCoeff_map_of_injective hinj] at h1
    simpa using h1
  by_contra hcon
  push_neg at hcon

  have hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p := by
    intro j hj
    have hk : 1 ≤ P.natDegree - j := by omega
    have hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j) := by
      rw [coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega,
        ← hP, coeff_map]
    have hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j) :=
      ⟨P.coeff j, hrev.symm⟩
    have := algebraMap_normCoeff φ hφ b _ hex
    rw [hrev] at this
    have := hinj this
    rw [← this]
    exact hcon _ hk

  set M := TensorProduct A K B
  have hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))
    have h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := LinearMap.congr_fun h2 1
    simpa using h3
  have hker : Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
      ← Polynomial.aeval_map_algebraMap K, hP]
    exact hCH

  let I : Ideal B := RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  have hI : I.comap (algebraMap A B) ≤ p := by
    intro a ha
    obtain ⟨Q₀, hQ₀p, hQ₀c⟩ := hQ₀
    have ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0 := ha
    have := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (TensorProduct.mk A K B 1)).1 ha'
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    have hs0' : φ (s * a) = 0 := by
      rw [map_mul]; simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hs0
    have hmem : s * a ∈ Q₀.comap φ := by simp [Ideal.mem_comap, hs0']
    rw [hQ₀c, Ideal.mem_bot] at hmem
    have hs' : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have : a = 0 := by
      rcases mul_eq_zero.1 hmem with h | h
      · exact absurd h hs'
      · exact h
    rw [this]; exact p.zero_mem
  haveI : Algebra.IsIntegral A B := inferInstance
  obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI
  have hPQ : Polynomial.aeval b P ∈ Q := hQI (by simpa [I, RingHom.mem_ker] using hker)
  have hbd : b ^ P.natDegree ∈ Q := by
    have hsum := hmon.as_sum

    rw [hsum, map_add (f := _), map_pow, aeval_X, map_sum] at hPQ
    refine (Q.add_mem_iff_left ?_).1 hPQ
    refine Q.sum_mem fun j hj => ?_
    rw [map_mul, aeval_C, aeval_X_pow]
    refine Q.mul_mem_right _ ?_
    have : P.coeff j ∈ Q.comap (algebraMap A B) := by
      change P.coeff j ∈ Ideal.under A Q
      rw [hQc]; exact hcoeff j (Finset.mem_range.1 hj)
    exact this
  exact hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)

end GlobalTheory.NormalDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReversedCharpolyCoeffNotMemPrimeStatement

section

@[expose] public section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  first | exact @GlobalTheory.NormalDescent.exists_normCoeff_not_mem | exact GlobalTheory.NormalDescent.exists_normCoeff_not_mem | (intros; apply GlobalTheory.NormalDescent.exists_normCoeff_not_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem mem_basicOpen_normCoeff_of_fibre {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) (h : ∀ y : Y, f y = x → y ∈ Y.basicOpen τ) :
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  have inj := hV.fromSpec.isOpenEmbedding.injective
  have h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥ := by
    let P0 : PrimeSpectrum Γ(X, V) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, hy⟩ := f.surjective (hV.fromSpec P0)
    have hyV : f y ∈ V := by
      have hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec := ⟨P0, rfl⟩
      rw [hV.range_fromSpec] at hr
      rw [hy]; exact hr
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hyV
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime
    (fun Q hQ hQp => by
      let q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V) := ⟨Q, hQ⟩
      have e : PrimeSpectrum.comap (f.app V).hom q = p := PrimeSpectrum.ext hQp
      exact (e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))
  exact ⟨k, hk, (e₁ _).2 hc⟩

end GlobalTheory.NormalDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X), x ∈ V →
    (∀ y : Y, f y = x → y ∈ Y.basicOpen τ) →
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  first | exact @GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | exact GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | (intros; apply GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormalDescent

theorem exists_sec_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X} (hM : M.IsLB) (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec,
      (∀ x : X, (∀ y : Y, f y = x → y ∈ nonzeroLocus t) → ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k)) ∧
      ∀ (x : X) (k : ℕ), 1 ≤ k → x ∈ nonzeroLocus (u k) → ∃ y ∈ nonzeroLocus t, f y = x := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sec_normCoeff_local' f hM t
  refine ⟨u, fun x hx => ?_, fun x k hk hx => ?_⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre f hV τ x hxV fun y hy => (ht y (hy ▸ hxV)).1 (hx y hy)
    exact ⟨k, hk, (hc k x hxV).2 h⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' f hV τ x k hxV hk ((hc k x hxV).1 hx)
    exact ⟨y, (ht y hxV).2 hy, rfl⟩

theorem isAmpleLB_of_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsFinite f → Function.Surjective f →
    ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  intro X X' f _ hN _ hs L hL h
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : Surjective f := ⟨hs⟩
  refine GlobalTheory.isAmpleLB_of_forall_le hL fun x U hx => ?_
  have hfin : (f ⁻¹' {x}).Finite := f.finite_preimage_singleton x
  obtain ⟨n, hn, s, hS, hle, -⟩ := h.exists_affine_finite_subset hfin (U := f ⁻¹ᵁ U)
    (fun y (hy : f y = x) => show f y ∈ U from hy ▸ hx)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu₁, hu₂⟩ := exists_sec_image f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hxk⟩ := hu₁ x fun y hy => ht.ge (hS hy)
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hxk, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hu₂ z k hk (e.le hz)
  exact hle (ht.le hw)

end GlobalTheory.NormalDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfPull

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteBase

theorem isAmpleLB_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) π → ∀ L : LB G.left, L.IsLB → IsAmpleLB (L.pull π) → IsAmpleLB L := by
  intro R R' _ _ _ _ _ _ _ _ _ _ ρ hinj hfin G _ G' _ π hG h L hL hA
  have := hG.smooth
  have := hG.quasiCompact
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hfin
  have hS : Surjective (spMap ρ) := ⟨hfin.to_isIntegral.comap_surjective hinj⟩
  have : IsFinite π := MorphismProperty.of_isPullback (P := @IsFinite) h.1.flip hF
  have hs : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hS
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hN : GlobalTheory.IsNormalScheme G.left := isNormalScheme_of_smooth G.hom
  exact GlobalTheory.NormalDescent.isAmpleLB_of_pull G.left G'.left π ⟨⟩
    (fun x => ⟨hN.1 x, hN.2 x⟩) inferInstance hs.surj L hL hA

end GlobalTheory.AmpleFiniteBase
end
end
