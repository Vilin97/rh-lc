module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphismStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransportStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateSequenceTransportStatement
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Mathlib.RepresentationTheory.Basic
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecomposition
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertiaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransportStatement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Formalism.ConjugateSelfDual.Statement
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem apply_eq_pow_cycMod_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω) {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have key := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω σ) ζ hζ
  simpa [cycMod, cycZ] using key

theorem cycMod_intrinsic : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ l _ r σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have h1 := apply_eq_pow_cycMod_val (F := F) (Ω := Ω) l r σ hζ.pow_eq_one
  have h2 := apply_eq_pow_cycMod_val (F := F') (Ω := Ω') l r (Φ σ) (ζ := E ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  rw [hΦ, h1, map_pow] at h2
  have hv := hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  apply Units.ext
  exact ZMod.val_injective _ hv.symm

end GlobalTheory.CompanionTheory.PTIso
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacterStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_equiv_cyclotomic_character : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecompositionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_equiv_transports_decomposition : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | exact GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquiv

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem isTotallyComplex_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F']
    [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  intro F F' _ _ _ _ e h
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have hr : (w.comap (e : F →+* F')).IsReal := (InfinitePlace.isReal_comap_iff e).2 hw
  exact InfinitePlace.not_isReal_iff_isComplex.2 (h.isComplex _) hr

end GlobalTheory.CompanionTheory.PTIso
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquivStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.totally_complex_of_ring_equiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtConclOfIsoOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace PositivityTheory.PTN

theorem ptConcl_of_iso_of (hL : PositivityTheory.PTN.LocHyp) : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → PTConclAt F' Ω' → PTConclAt F Ω := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE hPT
  intro l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.galois_group_transport_isomorphism F Ω F' Ω' e E hE
  obtain ⟨eO, eV, heO, hV, hV2, hN⟩ := GlobalTheory.T.ring_isomorphism_transports_places F F' e
  have hloc := hL F Ω F' Ω' e E hE Φ hΦ
  have hpl := GlobalTheory.T.ring_equiv_transports_decomposition F Ω F' Ω' e E hE eO eV heO hV
  have hcyc := GlobalTheory.T.ring_equiv_cyclotomic_character F Ω F' Ω' e E hE Φ hΦ l r
  obtain ⟨inv', hinv'⟩ := GlobalTheory.T.ring_equiv_transports_inertia F Ω F' Ω' e E hE Φ hΦ
    (fun A A' hA σ => (hloc A A' hA σ).1) l r hcyc inv

  let S' : Finset (HeightOneSpectrum (𝓞 F')) := S.map eV.toEmbedding
  have hSS : ∀ v, v ∈ (S : Set (HeightOneSpectrum (𝓞 F))) ↔
      eV v ∈ (S' : Set (HeightOneSpectrum (𝓞 F'))) := by
    intro v; simp [S']
  let eI : S ≃ S' := Equiv.subtypeEquiv eV (fun v => by simp [S'])
  have heI : ∀ v : S, (eI v : HeightOneSpectrum (𝓞 F')) = eV v := fun _ => rfl
  let Av' : S' → ValuationSubring Ω' := fun v' => (Av (eI.symm v')).comap E.symm.toRingHom
  have hAv'' : ∀ (v : S) (x : Ω), E x ∈ Av' (eI v) ↔ x ∈ Av v := by
    intro v x
    simp [Av', ValuationSubring.mem_comap]
  have hPl' : ∀ v' : S', IsPlaceOver (Av' v') v'.1 := by
    intro v'
    obtain ⟨v, rfl⟩ := eI.surjective v'
    exact (hpl _ _ (hAv'' v) v.1).1 (hAv v)

  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.galois_quotient_equiv_of_matching_places F Ω F' Ω' e E hE Φ hΦ eV hpl
    (fun A A' hA σ => (hloc A A' hA σ).2.1) _ _ hSS
  let μ' : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* (ZMod (l ^ r))ˣ :=
    μ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hμ' : μ'.comp (toGS Ω' _) = cycMod F' Ω' l r := by
    ext1 τ
    obtain ⟨σ, rfl⟩ := Φ.surjective τ
    have h1 : Ψ.symm (toGS Ω' _ (Φ σ)) = toGS Ω _ σ := by rw [← hΨ]; simp
    have h2 : μ (toGS Ω _ σ) = cycMod F Ω l r σ := DFunLike.congr_fun hμ σ
    show μ (Ψ.symm (toGS Ω' _ (Φ σ))) = _
    rw [h1, h2, hcyc]
  let ρ' : Representation (ZMod (l ^ r)) (GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F')))) M :=
    ρ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hρ' : ContAction ρ' := hρ.comp' Ψ.symm.continuous

  have hl' : l ≠ 2 ∨ IsTotallyComplex F' := hl.imp id (GlobalTheory.T.totally_complex_of_ring_equiv F F' e)
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  have hnorm' : InvNormalised (E ζ) inv' := by
    intro A' v' hP
    obtain ⟨v, rfl⟩ := eV.surjective v'
    let A : ValuationSubring Ω := A'.comap E.toRingHom
    have hA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => by simp [A, ValuationSubring.mem_comap]
    have hP0 : IsPlaceOver A v := (hpl A A' hA v).2 hP
    refine ⟨(hinv' A A' hA).1 (hinv A v hP0).1, ?_⟩
    exact GlobalTheory.T.ring_equiv_transports_residue F Ω F' Ω' e E hE Φ hΦ eO eV heO hV hV2 hN l r hcyc A A' hA (hloc A A' hA) ζ v
      (inv A) (inv' A') (hinv' A A' hA).2 (hinv A v hP0).2
  have hS' : ContainsAbove S' l := by
    intro v' hv'
    obtain ⟨v, rfl⟩ := eV.surjective v'
    have : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [hV, map_natCast]; exact hv'
    exact Finset.mem_map_of_mem _ (hS v this)
  obtain ⟨h9, hsha⟩ := hPT l r hl' hr (E ζ) hζ' inv' hnorm' S' hS' Av' hPl' μ' hμ' M ρ' hρ'

  let eD : ∀ v : S, Dec (F := F) (Av v) ≃ₜ* Dec (F := F') (Av' (eI v)) := fun v =>
    subgroupIso Φ _ _ (fun σ => (hloc _ _ (hAv'' v) σ).1)
  have hcomp : ∀ (v : S) (d : Dec (F := F) (Av v)),
      locFam S' Av' (eI v) (eD v d) = Ψ (locFam S Av v d) := by
    intro v d
    exact (hΨ (d : G F Ω)).symm
  have hχ : ∀ g, μ' (Ψ g) = μ g := fun g => by simp [μ']
  have hρc : ∀ g m, ρ' (Ψ g) m = ρ g m := fun g m => by simp [ρ']
  refine ⟨?_, ?_⟩
  · refine (nineTermExact_iff S Av μ _ ρ hρ).2 ?_
    refine GlobalTheory.T.poitou_tate_sequence_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av') (continuous_locFam S' Av')
      μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc _ _ hρ hρ' ?_ ((nineTermExact_iff S' Av' μ' _ ρ' hρ').1 h9)
    intro v z z' hz
    refine (hinv' _ _ (hAv'' v)).2 (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v) z)
      (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S' Av' μ' hμ' (eI v)) z') ?_
    intro g h g' h' hg hh
    have e1 : g' = eD v g := Subtype.ext hg
    have e2 : h' = eD v h := Subtype.ext hh
    subst e1 e2
    exact hz g h
  · exact (shaDual_iff S Av μ ρ).2 (GlobalTheory.T.tate_shafarevich_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av')
      (continuous_locFam S' Av') μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc ((shaDual_iff S' Av' μ' ρ').1 hsha))

end PositivityTheory.PTN
end
end
end
