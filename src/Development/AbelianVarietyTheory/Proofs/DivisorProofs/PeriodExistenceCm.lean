module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleClassIdentityComponentIffArtinKernelStatement
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAtStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriodStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra; ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic) (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point), GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ), GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ → ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  first | exact @GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | exact GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | (intros; apply GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEquiStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K, Continuous φ ∧ Function.Bijective φ ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  first | exact @GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | exact GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abMap_of_algEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOne

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.InertiaRestrict

theorem restrict_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  intro K _ _ Ω _ _ _ e L h v hv A hA σ hσ
  haveI := h.isGalois
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  have hint : ∀ y : 𝓞 L, e.symm ((y : L) : AlgebraicClosure K) ∈ A := by
    intro y
    have h1 : IsIntegral ℤ (e.symm ((y : L) : AlgebraicClosure K)) :=
      map_isIntegral_int ((e.symm : AlgebraicClosure K →+* Ω).comp (algebraMap L (AlgebraicClosure K)))
        y.isIntegral_coe
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (h1.tower_top)
    rw [← ha]
    exact a.2
  let φ : 𝓞 L →+* A :=
    { toFun := fun y => ⟨e.symm ((y : L) : AlgebraicClosure K), hint y⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ
  have hmem : ∀ y : 𝓞 L, y ∈ Q ↔ A.valuation (e.symm ((y : L) : AlgebraicClosure K)) < 1 := fun y =>
    ValuationSubring.valuation_lt_one_iff A (φ y)
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI hQo : Q.LiesOver v.asIdeal := by
    constructor
    ext x
    rw [Ideal.under, Ideal.mem_comap, hmem, ← hA x]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := by
      first
        | rfl
        | (rw [RingOfIntegers.algebraMap_coe]; rfl)
        | simp [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)]
    rw [this, AlgEquiv.commutes]
  have hram : Q.ramificationIdx (𝓞 K) = 1 := hv Q hQp hQo
  have hcard : Nat.card (Q.inertia (L ≃ₐ[K] L)) = 1 := by
    have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
    have hpr : (Q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ Q
    have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under (𝓞 K)) Q
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q (L ≃ₐ[K] L), hram] at hc
  have hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ := Subgroup.card_eq_one.1 hcard
  have hin : AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) ∈ Q.inertia (L ≃ₐ[K] L) := by
    refine AddSubgroup.mem_inertia.mpr fun y => ?_
    change _ ∈ Q
    rw [hmem]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y - y : 𝓞 L) : L) : AlgebraicClosure K)
        = e (σ (e.symm ((y : L) : AlgebraicClosure K))) - ((y : L) : AlgebraicClosure K) := by
      have h3 : ((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) =
          AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) (y : L) := rfl
      simp only [map_sub, h3, AlgEquiv.restrictNormalHom_apply]
      have h4 := AlgEquiv.restrictNormalHom_apply L ((e.symm.trans σ).trans e) (y : L)
      rw [AddSubgroupClass.coe_sub, h4]
      rfl
    rw [h2, map_sub, AlgEquiv.symm_apply_apply]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hint y))
  rw [hbot] at hin
  exact hin

end GlobalTheory.InertiaRestrict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  first | exact @GlobalTheory.InertiaRestrict.restrict_eq_one | exact GlobalTheory.InertiaRestrict.restrict_eq_one | (intros; apply GlobalTheory.InertiaRestrict.restrict_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedIdeleEqLocalIdele

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.Div.SuppIdele

theorem snd_apply_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : AdeleRing (𝓞 K) K) : (a * b).2 v = a.2 v * b.2 v := rfl

theorem supported_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K},
    IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧
      localIdele K v x = a := by
  intro K _ _ v a ha
  classical
  let x : (v.adicCompletion K)ˣ :=
    { val := (a : AdeleRing (𝓞 K) K).2 v
      inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v
      val_inv := by
        rw [← snd_apply_mul, Units.mul_inv]; rfl
      inv_val := by
        rw [← snd_apply_mul, Units.inv_mul]; rfl }
  refine ⟨x, rfl, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact (ha.1 w).symm
  · apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst hw
      exact (localIdele_snd_self K w x).trans rfl
    · exact ((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm

end GlobalTheory.Div.SuppIdele
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedIdeleEqLocalIdeleStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.supportedIdele_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K}, IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧ localIdele K v x = a := by
  first | exact @GlobalTheory.Div.SuppIdele.supported_eq_localIdele | exact GlobalTheory.Div.SuppIdele.supported_eq_localIdele | (intros; apply GlobalTheory.Div.SuppIdele.supported_eq_localIdele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal

open Neutral.B1

theorem exists_uniformisation_torsTransport {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ≠ 0) :
    letI : Algebra K ℂ := ι.toAlgebra
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ :=
  GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod h2 ι Λ₀ Ω₀ hΛ hΩ

theorem exists_globalArtinMap {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (e : Ω ≃ₐ[K] AlgebraicClosure K) :
    ∃ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art ∧
      ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
        Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  obtain ⟨φ, hφc, hφb, hφ⟩ := GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv e
  let ψ : Ideles K →* Field.absoluteGaloisGroupAbelianization K := φ.comp art⁻¹
  have hψ : ∀ s, ψ s = φ (art s)⁻¹ := fun s => rfl
  have hle : (diagUnits K).range ≤ ψ.ker := by
    rintro _ ⟨k, rfl⟩
    have hk : diagUnits K k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    rw [MonoidHom.mem_ker, hψ, MonoidHom.mem_ker.mp hk, inv_one, map_one]
  let Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K := QuotientGroup.lift _ ψ hle
  have hArt : ∀ s, Art (QuotientGroup.mk s) = φ ((art s)⁻¹) := fun s => rfl
  have hArtσ : ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
      Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := fun s σ h => by
    rw [hArt, h, hφ]
  refine ⟨Art, ⟨?_, ?_, ?_, ?_, ?_⟩, hArtσ⟩
  · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    exact hφc.comp (ha.quot.continuous.inv)
  · intro c
    obtain ⟨y, rfl⟩ := hφb.2 c
    obtain ⟨x, rfl⟩ := ha.quot.surjective y
    exact ⟨QuotientGroup.mk x⁻¹, by rw [hArt, map_inv art, inv_inv]⟩
  · ext c
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hArt, GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel ha,
      ← map_one φ, hφb.1.eq_iff, inv_eq_one]
  · intro L h v hv a hsupp
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.supportedIdele_eq_localIdele hsupp
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
    constructor
    · intro hu Q hQ hQv
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.frob v A hA (art (localIdele K v x))).1
        ⟨x, (GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt v x).1 hu, rfl⟩
      rw [hArtσ _ σ (by rw [← hσe, map_inv, inv_inv]), abRestrict_mk]
      exact GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension e L h v A hA σ hσ Q hQ hQv
    · intro hu
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.ine v A hA (art (localIdele K v x))).1 ⟨x, hu, rfl⟩
      rw [hArtσ _ σ⁻¹ (by rw [← hσe, map_inv]), abRestrict_mk]
      exact GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one e L h v hv A hA σ⁻¹ ((ReciprocityTheory.Gal.Ine A).inv_mem hσ)
  · intro L h w hw
    exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))

theorem periodEx_of_mainTheorem : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  intro hMT K _ _ _ ι h2 Λ₀ Ω₀ hΛ hΩ Ω _ _ _ j art hj ha g σ t hσg hsym
  letI : Algebra K ℂ := ι.toAlgebra
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← hj, RingHom.comp_apply, ← hσg, AlgEquiv.commutes]
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨X, hX, ξ, hξ, hT⟩ := exists_uniformisation_torsTransport h2 ι Λ₀ Ω₀ hΛ hΩ
  let e := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  obtain ⟨Art, hArt, hArtσ⟩ := exists_globalArtinMap ha e
  have hjK : ∀ x : K, j (algebraMap K Ω x) = algebraMap K ℂ x := fun x => by
    rw [← RingHom.comp_apply, hj]
    rfl
  let jK : Ω →ₐ[K] ℂ := { j with commutes' := hjK }
  have hR : GlobalTheory.EllipticCM.RestrictsTo gK (Art (QuotientGroup.mk (finIdele K t))) := by
    rw [hArtσ _ σ hsym]
    refine ⟨jK.comp e.symm.toAlgHom, (e.symm.trans σ).trans e, fun x => ?_, rfl⟩
    change g (j (e.symm x)) = j (e.symm (e (σ (e.symm x))))
    rw [AlgEquiv.symm_apply_apply, hσg]
  have hTr := hMT K h2 Art hArt gK (finIdele K t) hR X 1 one_ne_zero ξ hξ
  rw [show GlobalTheory.EllipticCM.finitePart (finIdele K t) = t from GlobalTheory.EllipticCM.finitePart_inr t] at hTr
  exact hT gK t hTr

end GlobalTheory.LatVal
end
end
end
