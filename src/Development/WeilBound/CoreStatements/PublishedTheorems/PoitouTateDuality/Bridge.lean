module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Formalism.ConjugateSelfDual.Statement
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtConclOfIsoOf

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInv

theorem nonempty_H2_muLoc_equiv_zmod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  intro F Ω _ _ _ _ _ l _ r hr A v hA
  exact (GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
    (GlobalTheory.TameQuot.contAction_muDec A l r)).1

end GlobalTheory.CompanionTheory.LocalInv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquivStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.local_brauer_roots_unity_equiv : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | exact GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | (intros; apply GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.local_invariant_cup_uniformizer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | exact GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | (intros; apply GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExists

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.normalised_local_invariant_exists : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r), Function.Bijective f ∧ IsNormalised ζ A v f := by
  first | exact @GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | exact GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | (intros; apply GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvFamNormalised

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.PoitouTateInv

theorem exists_invFam_normalised : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω,
    IsPrimitiveRoot ζ (l ^ r) → ∃ inv : InvFam F Ω l r,
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A) := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ
  classical
  have key := GlobalTheory.T.normalised_local_invariant_exists F Ω l r hr ζ hζ
  refine ⟨fun A => if h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v then
    Classical.choose (key A h.choose h.choose_spec) else 0, fun A v hv => ?_⟩
  have h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v := ⟨v, hv⟩
  have e : h.choose = v := eq_of_isPlaceOver h.choose_spec hv
  have spec := Classical.choose_spec (key A h.choose h.choose_spec)
  simp only [dif_pos h]
  generalize Classical.choose (key A h.choose h.choose_spec) = f at spec ⊢
  rw [e] at spec
  exact spec

end GlobalTheory.CompanionTheory.PoitouTateInv

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSubfieldModel

section

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bridge

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem ptConclAt_all_of (hfs : PtfsHyp) (hL : LocHyp) :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      PTConclAt F Ω := by
  intro F Ω _ _ _ _ _
  obtain ⟨K, hK, hC, e, E, h⟩ := GlobalTheory.CompanionTheory.FieldModel.exists_subfield_model F Ω
  exact ptConcl_of_iso_of hL F Ω K (AlgebraicClosure ℚ) e E h (hfs K)

theorem poitouTateNormalised_of (hfs : PtfsHyp) (hL : LocHyp) (hvan : VanishAll) :
    PoitouTateNormalised := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, hinv⟩ := GlobalTheory.CompanionTheory.PoitouTateInv.exists_invFam_normalised F Ω l r hr ζ hζ
  refine ⟨inv, hinv, ?_⟩
  intro S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have h := ptConclAt_all_of hfs hL F Ω l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨h.1, h.2, hvan F Ω l r hl hr S hS M ρ hρ⟩

end PositivityTheory.PTN
end
end
end
