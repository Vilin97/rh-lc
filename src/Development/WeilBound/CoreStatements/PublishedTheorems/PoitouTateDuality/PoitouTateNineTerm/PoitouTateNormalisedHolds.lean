module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
public import Mathlib.RingTheory.PicardGroup
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.NineAddCore
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIso
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficientsStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bridge
public import ReciprocityTheory.GaloisValuations.Global
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Mathlib.RepresentationTheory.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHypOfCmp
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocalCmp2

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem localCmp2' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      (∀ (v : S) σ x, ιs ⟨v.1, Finset.mem_coe.2 v.2⟩
        (((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) =
          σ (ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ x)) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ x => hι v σ x, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsDataEx

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem foundData_nonempty (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) :
    Nonempty (FoundData Kf S l r ζ Av μ M ρ) := by
  obtain ⟨e, he⟩ := gsEquiv_toGS' Kf.1 (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  obtain ⟨ιs, ev, hc, hι, hev⟩ := localCmp2' Kf.1 S Av hAv e he
  obtain ⟨A, hA, eM, hM⟩ := repCmp e ρ hρ
  obtain ⟨eD, hD, hDζ⟩ := dualCmp' Kf S hr ζ hζ hS e he μ hμ ρ A eM hM
  exact ⟨⟨e, he, ιs, ev, hc, hev, hι, A, hA, eM, hM, eD, hD, hDζ⟩⟩

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.VanishAll

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory.CompanionTheory.GSCd.Transport

namespace PositivityTheory.Lit1.GFVanish

theorem exists_gs_transport_field (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) :
    ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧
      Nonempty (F ≃+* K.1) ∧
      Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1)))) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨K, ψ, e, he⟩ := exists_embedded F Ω
  classical
  refine ⟨K, S.map (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding, ?_, ⟨ψ⟩,
    nonempty_gal ψ e he ?_⟩
  · intro w hw
    have hv : (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S := by
      apply hS
      change RingOfIntegers.mapRingEquiv ψ (l : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_map.2 ⟨_, hv, (placeEquiv _).apply_symm_apply w⟩
  · intro v
    simp

theorem cdp_gal_le_two_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F) :
    cdp l (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) ≤ 2 := by
  obtain ⟨K, S', hS', ⟨ψ⟩, ⟨e⟩⟩ := exists_gs_transport_field F Ω l S hS
  rw [GlobalTheory.T.cohomological_dimension_topological_iso _ _ l e]
  refine cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out
    (fun v hv => hS' v hv) (hK.imp id fun h => by
      let _ : IsTotallyComplex F := h
      let _ : Algebra F K.1 := ψ.toRingHom.toAlgebra
      exact isTotallyComplex_of_algebra F K.1)

theorem subsingleton_hn_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
    [IsDiscreteRep A] (hA : ∀ a : A.V, (l ^ r) • a = 0) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (cohomology A n) := by
  have hp : l.Prime := Fact.out
  have hcd := cdp_gal_le_two_gen F Ω l S hS hK
  refine subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero)
    (fun q hq hqd => ?_) A hA hn
  have hql : q = l := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hql
  exact hcd

theorem vanishAll : PositivityTheory.PoitouTateConclusion.VanishAll := by
  intro F Ω _ _ _ _ _ l _ r hK _ S hS M _ _ _ _ _ ρ hc n hn
  obtain ⟨A, _, _, hA, -, -, hAn⟩ := PositivityTheory.Lit1.GFTransport.cohDict S ρ hc
  obtain ⟨en⟩ := hAn n
  have : Subsingleton (cohomology A n) := subsingleton_hn_gen F Ω l r S hS hK A hA n hn
  exact en.toEquiv.subsingleton

end PositivityTheory.Lit1.GFVanish
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.MemDecompositionSubgroupIff

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise

namespace PositivityTheory.PTNLoc

theorem mem_decompositionSubgroup_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    exact ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : G F Ω) y)
    rw [ReciprocityTheory.Gal.mul_inv_apply] at this
    exact this.symm

theorem valuation_le_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff]
  exact hA x

theorem valuation_lt_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) < 1 ↔ A.valuation x < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x,
    hA, hA, map_eq_zero_iff E E.injective]

theorem locHyp : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ
  have hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F' := by
    rw [mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, hA, hA]
      exact h x
    · intro h x
      have := h (E x)
      rwa [hΦ, hA, hA] at this
  refine ⟨hdec, ?_, fun q => ?_⟩
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_sub E, valuation_lt_one_transport E hA] at this
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA] at this

end PositivityTheory.PTNLoc
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNormalisedOfNine

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem locHyp_holds : LocHyp := PositivityTheory.PTNLoc.locHyp

theorem poitouTateNormalised_of_ptfs (hfs : PtfsHyp) (hvan : VanishAll) :
    PoitouTateNormalised :=
  poitouTateNormalised_of hfs locHyp_holds hvan

theorem poitouTateNormalised_of_cmp (hN : PositivityTheory.Lit1.PTN.NineCmpFS) (hS : PositivityTheory.Lit1.PTN.ShaCmpFS) :
    PoitouTateNormalised :=
  poitouTateNormalised_of_ptfs (PositivityTheory.Lit1.PTN.ptfsHyp_of_cmp hN hS) PositivityTheory.Lit1.GFVanish.vanishAll

theorem poitouTateNormalised_of_nine (hN : PositivityTheory.Lit1.PTN.NineCmpFS) : PoitouTateNormalised :=
  poitouTateNormalised_of_cmp hN PositivityTheory.Lit1.PTN.shaCmpFS'

end PositivityTheory.PTN
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem nineAddFS_V : NineAddFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact (foundData_nonempty ⟨K, inferInstance⟩ S hr ζ hζ hS Av hAv μ hμ ρ hρ).elim fun d =>
    nineAdd_core ⟨K, inferInstance⟩ hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ d

theorem poitouTateNormalised_holds : GlobalTheory.Published.PoitouTateNormalised :=
  PositivityTheory.PTN.poitouTateNormalised_of_nine (nineCmpFS_of_nineAddFS nineAddFS_V)

end PositivityTheory.Lit1.PTN
end
end
end
