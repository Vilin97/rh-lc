module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import ReciprocityTheory.NeutralLocalFields.HilbertClassField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.GaloisValuations.GlobalA
public import ReciprocityTheory.GaloisValuations.Global
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocityStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  first | exact @GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | exact GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | (intros; apply GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugation

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

namespace GlobalTheory

theorem complexConjugation_mul_self {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (c : Ω ≃ₐ[E] Ω) (hc : IsComplexConjugation c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  show j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

theorem not_isComplexConjugation_of_nrRealPlaces_eq_zero {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (hE : InfinitePlace.nrRealPlaces E = 0)
    (c : Ω ≃ₐ[E] Ω) : ¬ IsComplexConjugation c := by
  rintro ⟨j, hj⟩
  let φ : E →+* ℂ := j.comp (algebraMap E Ω)
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    show starRingEnd ℂ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)
    rw [← hj, AlgEquiv.commutes]
  have hw : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
  have : IsEmpty {w : InfinitePlace E // w.IsReal} := by
    classical
    rw [InfinitePlace.nrRealPlaces] at hE
    exact Fintype.card_eq_zero_iff.mp (by convert hE)
  exact this.false ⟨_, hw⟩

theorem addHom_complexConjugation_eq_zero : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  intro E Ω _ _ _ _ l _ O _ _ hl M _ _ z hz c hc
  rcases hl with hl | hE
  · have h1 : z 1 = 0 := by
      have := hz 1 1
      simp only [mul_one] at this
      simpa using this
    have h2 : z c + z c = 0 := by
      rw [← hz, show (c * c : G E Ω) = 1 from complexConjugation_mul_self c hc, h1]
    have hu : IsUnit (2 : ℤ_[l]) := by
      have := (PadicInt.norm_natCast_eq_one_iff (p := l) (n := 2)).mpr
        ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl)
      rw [PadicInt.isUnit_iff]; exact_mod_cast this
    have hu' : IsUnit (2 : O) := by
      have := hu.map (algebraMap ℤ_[l] O)
      rwa [map_ofNat] at this
    have h3 : (2 : O) • z c = 0 := by rw [two_smul]; exact h2
    exact (hu'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)
  · exact absurd hc (not_isComplexConjugation_of_nrRealPlaces_eq_zero hE c)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.galoisAddHom_vanishes_complexConjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  first | exact @GlobalTheory.addHom_complexConjugation_eq_zero | exact GlobalTheory.addHom_complexConjugation_eq_zero | (intros; apply GlobalTheory.addHom_complexConjugation_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertia

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
open Pointwise

namespace GlobalTheory.HilbertKill

theorem hilbertSubgroup_le_ker : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  intro E Ω _ _ _ _ _ Av hAv M _ z hz hlc hIne hC
  let f : G E Ω →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by
        have h := hz 1 1
        rw [mul_one, left_eq_add] at h
        simp [h]
      map_mul' := fun g h => by simp [hz] }
  have hf : ∀ g, g ∈ f.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  have hclosed : IsClosed (f.ker : Set (G E Ω)) := by
    convert hlc.isClosed_fiber 0 using 1
    ext g
    exact hf g
  have hinv : ∀ g, z g⁻¹ = - z g := fun g => by
    have h := hz g g⁻¹
    have h1 : z 1 = 0 := (hf 1).1 f.ker.one_mem
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  intro σ hσ
  refine (hf σ).1 (Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hclosed hσ)
  rintro g ((hg | ⟨A, hg⟩) | hg)
  · exact Abelianization.commutator_subset_ker f hg
  · have hg' := (ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg
    rcases GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩
    · exact f.ker.one_mem
    have hA : IsPlaceOver A v := fun x => by rw [← hv x, A.mem_nonunits_iff]
    have hgI : g ∈ Ine (F := E) A :=
      ⟨hg'.1, fun x hx => A.mem_nonunits_iff.1 (hg'.2 x ((A.valuation_le_one_iff x).1 hx))⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (hAv v) hA
    have h2 : τ⁻¹ * g * τ⁻¹⁻¹ ∈ Ine (F := E) (τ⁻¹ • A) := conj_mem_Ine_smul hgI
    rw [inv_inv, ← hτ, inv_smul_smul] at h2
    have h3 := hIne v _ h2
    show z g = 0
    have e : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
    rw [e, hz, hz, h3, hinv, add_zero, add_neg_cancel]
  · exact (hf g).2 (hC g hg)

end GlobalTheory.HilbertKill
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertiaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  first | exact @GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | exact GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | (intros; apply GlobalTheory.HilbertKill.hilbertSubgroup_le_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec

section

@[expose] public section

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.UnramifiedClassBound
open Neutral.HilbertClassField

theorem vhE_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ReciprocityTheory.ChartRestriction.T2.VhE := by
  intro E Ω _ _ _ _ _ Av hAv l _ O _ _ _ _ _ hl M _ _ hM ρ hρ S hS hU
  obtain ⟨eM⟩ := hM
  obtain ⟨art, hsurj, hker, -⟩ := GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity hA E Ω

  let ψ : (Additive (ClassGroup (𝓞 E)) →+ M) →ₗ[O] coZ1s ρ :=
    { toFun := fun f => ⟨fun g => f (Additive.ofMul (art g)), fun g h => by
        show f (Additive.ofMul (art (g * h))) = f (Additive.ofMul (art g)) + ρ g (f (Additive.ofMul (art h)))
        rw [hρ, map_mul, ofMul_mul, map_add (f := _)]⟩
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
  let Φ := (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype)) ∘ₗ ψ
  have hle : S ≤ LinearMap.range Φ := by
    intro x hx
    obtain ⟨z, rfl, hlc⟩ := hS x hx
    have hz : ∀ g h : G E Ω, (z : G E Ω → M) (g * h) = (z : G E Ω → M) g + (z : G E Ω → M) h := by
      intro g h
      have := z.2 g h
      rw [hρ] at this
      exact this
    have hI : ∀ v, ∀ σ ∈ Ine (F := E) (Av v), (z : G E Ω → M) σ = 0 := by
      intro v σ hσ
      have h1 := hU v hx
      rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨w, hw⟩ := h1
      have := congrFun hw ⟨σ, hσ⟩
      simp only [coD0, resRep, LinearMap.coe_mk, AddHom.coe_mk] at this
      exact (show (z : G E Ω → M) σ = _ from this.symm).trans (by simp [hρ])
    have hkill := GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia E Ω Av hAv M z hz hlc hI (fun c hc => GlobalTheory.T.galoisAddHom_vanishes_complexConjugation E Ω l O hl M z hz c hc)
    let zH : G E Ω →* Multiplicative M :=
      { toFun := fun g => Multiplicative.ofAdd ((z : G E Ω → M) g)
        map_one' := by
          have := hz 1 1
          simp only [mul_one] at this
          have h0 : (z : G E Ω → M) 1 = 0 := by
            have := congrArg (fun t => t - (z : G E Ω → M) 1) this
            simpa using this.symm
          simp [h0]
        map_mul' := fun g h => by simp [hz g h] }
    have hk : art.ker ≤ zH.ker := by
      intro σ hσ
      rw [hker] at hσ
      simp [zH, MonoidHom.mem_ker, hkill σ hσ]
    let Lf := (MonoidHom.liftOfSurjective art hsurj) ⟨zH, hk⟩
    let f : Additive (ClassGroup (𝓞 E)) →+ M :=
      { toFun := fun a => Multiplicative.toAdd (Lf (Additive.toMul a))
        map_zero' := by simp
        map_add' := fun a b => by simp }
    refine ⟨f, ?_⟩
    change Submodule.mkQ _ (ψ f) = Submodule.mkQ _ z
    congr 1
    apply Subtype.ext
    funext g
    show Multiplicative.toAdd (Lf (art g)) = (z : G E Ω → M) g
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  calc Module.length O S ≤ Module.length O (LinearMap.range Φ) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ Module.length O (Additive (ClassGroup (𝓞 E)) →+ M) :=
        Module.length_le_of_surjective Φ.rangeRestrict Φ.surjective_rangeRestrict
    _ ≤ _ := by
        have := GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le l O M eM (Additive (ClassGroup (𝓞 E)))
        rwa [show Nat.card (Additive (ClassGroup (𝓞 E))) = classNumber E from by
          rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]; rfl] at this
end GlobalTheory.UnramifiedClassBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ReciprocityTheory.ChartRestriction.T2.VhE := by
  first | exact @GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | exact GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | (intros; apply GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity <;> assumption)
end
end
