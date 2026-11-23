module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import Mathlib.RingTheory.PicardGroup
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
public import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDefs
public import ReciprocityTheory.GaloisValuations.Global
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
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
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSide
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.LocalFields.FilteredSurj
import GroundTheory.ProfiniteCohomology.ProcyclicDefs
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import Mathlib.RepresentationTheory.Rep.Basic
import Formalism.ConjugateSelfDual.Statement

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsChi

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion ValuativeRel

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem natCast_card_pow_sub_one_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[v.adicCompletion F] ^ n - 1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h
  have h1 := (GroundTheory.Global.ringOfIntegersToInteger_mem_maximalIdeal_iff v _).2 h
  rw [map_natCast] at h1
  apply GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero (K := v.adicCompletion F) hn
  rw [← map_natCast (IsLocalRing.residue 𝒪[v.adicCompletion F])]
  exact (IsLocalRing.residue_eq_zero_iff _).2 h1

theorem valuation_le_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ}
    (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : A.valuation x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have : A.valuation x ^ m = 1 := by rw [← Valuation.map_pow, hx, Valuation.map_one]
  exact (one_lt_pow₀ h hm).ne' this


theorem exists_chi' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (v : HeightOneSpectrum (𝓞 Kf.1)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v)
    (N : ℕ+)
    (ι : AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure (v.adicCompletion Kf.1))
    (ev : (AlgebraicClosure (v.adicCompletion Kf.1) ≃ₐ[v.adicCompletion Kf.1]
        AlgebraicClosure (v.adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ι (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ι x)) :
    ∃ χ : Dec (F := Kf.1) A → ZMod (N : ℕ),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A, IsFrob (F := Kf.1) A (normV v) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := by

  classical
  have hm0 : (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) ≠ 0 := by
    have := GroundTheory.LocalField.one_lt_card_residueField_pow (K := v.adicCompletion Kf.1) N.ne_zero
    omega
  haveI : NeZero (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := ⟨hm0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1)
  have hιξ : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := hξ.map_of_injective ι.toRingHom.injective
  have hmA : ¬ A.valuation (((Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) : ℕ) : AlgebraicClosure ℚ) < 1 := by
    intro h
    apply natCast_card_pow_sub_one_notMem Kf.1 v N.ne_zero
    refine (hA _).1 ?_
    simpa using h
  let χ : Dec (F := Kf.1) A → ZMod (N : ℕ) := fun g =>
    urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N (ev.symm g)
  have hχ : ∀ g, χ g = unramifiedCoord (v.adicCompletion Kf.1) (ev.symm g) N := fun g => rfl
  have hχev : ∀ σ, χ (ev σ) =
      urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := fun σ => by
    show urChar _ _ N (ev.symm (ev σ)) = _
    rw [MulEquiv.symm_apply_apply]
  clear_value χ
  have key : ∀ (g : Dec (F := Kf.1) A) (a : ℕ),
      (a : ZMod (N : ℕ)) = χ g ↔ (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] ^ a := by
    intro g a
    rw [hχ, natCast_eq_unramifiedCoord_iff hιξ (ev.symm g) a, ← hev (ev.symm g) ξ,
      MulEquiv.apply_symm_apply, ← map_pow]
    exact ι.toRingHom.injective.eq_iff
  refine ⟨χ, fun g h => ?_, fun g hg => ?_, fun g hg => ?_, ?_, fun σ => ?_⟩
  · rw [hχ, hχ, hχ, map_mul, unramifiedCoord_mul]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one]) hξ.pow_eq_one hgx
    have := (key g 0).2 (by rw [pow_zero, pow_one]; exact e)
    rw [← this, Nat.cast_zero]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have hN : normV v = Nat.card 𝓀[v.adicCompletion Kf.1] := (natCard_residueField_integer v).symm
    rw [hN] at hgx
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one])
        (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) hgx
    have := (key g 1).2 (by rw [pow_one]; exact e)
    rw [← this, Nat.cast_one]
  · refine continuous_def.2 fun s _ => ?_
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨Subtype.val ⁻¹' {τ : G Kf.1 (AlgebraicClosure ℚ) | τ ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ},
      fun g' hg' => ?_, continuous_subtype_val.isOpen_preimage _
        (isOpen_setOf_apply (F := Kf.1) ξ (fun y => y = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ)), rfl⟩
    have h1 := (key g (χ g).val).1 (ZMod.natCast_zmod_val _)
    have h2 : (((χ g).val : ℕ) : ZMod (N : ℕ)) = χ g' := (key g' (χ g).val).2 (by
      rw [show (g' : G Kf.1 (AlgebraicClosure ℚ)) ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ from hg', h1])
    rw [ZMod.natCast_zmod_val] at h2
    show χ g' ∈ s
    rw [← h2]; exact hg
  · exact hχev σ

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsKummer

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_kummer' (F : Type) [Field F] [NumberField F] {l r : ℕ} [Fact l.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra F (AlgebraicClosure ℚ)]
    [IsAlgClosure F (AlgebraicClosure ℚ)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (a : F) (ha : a ≠ 0)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap F (AlgebraicClosure ℚ) a) :
    ∃ κ : Dec (F := F) A → ZMod (l ^ r),
      (∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y) ∧
      Continuous κ ∧
      ∀ g h : Dec (F := F) A, κ (g * h) =
        κ g + ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) * κ h := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero r (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hN0⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at hy
    exact ha ((algebraMap F (AlgebraicClosure ℚ)).injective (by rw [← hy, map_zero]))

  have hroot : ∀ σ : G F (AlgebraicClosure ℚ), (σ y / y) ^ (l ^ r) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy, div_self (pow_ne_zero _ hy0)]
  have hex : ∀ σ : G F (AlgebraicClosure ℚ), ∃ i < l ^ r, ζ ^ i = σ y / y := fun σ => hζ.eq_pow_of_pow_eq_one (hroot σ)
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ a ≡ b [MOD l ^ r] := by
    intro a b
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ r) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    have e : ζ ^ a = ζ ^ b ↔ (hζ.isUnit hN0).unit ^ a = (hζ.isUnit hN0).unit ^ b := by
      rw [Units.ext_iff]; simp
    rw [e, pow_eq_pow_iff_modEq, ← hu.eq_orderOf]

  have huniq : ∀ a b : ℕ, ζ ^ a * y = ζ ^ b * y → (a : ZMod (l ^ r)) = b := by
    intro a b h
    have h' : ζ ^ a = ζ ^ b := mul_right_cancel₀ hy0 h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hmod a b).mp h')
  let κ : Dec (F := F) A → ZMod (l ^ r) := fun g => ((hex (g : G F (AlgebraicClosure ℚ))).choose : ZMod (l ^ r))
  have hκ : ∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y := by
    intro g
    have h1 := (hex (g : G F (AlgebraicClosure ℚ))).choose_spec
    have hv : (κ g).val = (hex (g : G F (AlgebraicClosure ℚ))).choose := ZMod.val_cast_of_lt h1.1
    rw [hv, h1.2, div_mul_cancel₀ _ hy0]
  have hκ_iff : ∀ (g : Dec (F := F) A) (b : ZMod (l ^ r)),
      κ g = b ↔ (g : G F (AlgebraicClosure ℚ)) y = ζ ^ b.val * y := by
    intro g b
    constructor
    · rintro rfl; exact hκ g
    · intro h
      have := huniq _ _ ((hκ g).symm.trans h)
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have : Algebra.IsIntegral F (AlgebraicClosure ℚ) := by
    have : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := IsAlgClosure.isAlgebraic
    infer_instance
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [continuous_discrete_rng]
    intro b
    have hset : κ ⁻¹' {b} = Subtype.val ⁻¹' {τ : G F (AlgebraicClosure ℚ) | τ y = ζ ^ b.val * y} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact hκ_iff g b
    rw [hset]
    exact (isOpen_setOf_apply (F := F) y (fun z => z = ζ ^ b.val * y)).preimage continuous_subtype_val
  · intro g h
    set c := ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) with hc
    have hgζ : (g : G F (AlgebraicClosure ℚ)) ζ = ζ ^ c.val := by
      have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
        (MulSemiringAction.toRingAut (G F (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (g : G F (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one
      exact hspec.trans (by rw [hc]; rfl)
    rw [hκ_iff]
    have e1 : ((g * h : Dec (F := F) A) : G F (AlgebraicClosure ℚ)) y = (g : G F (AlgebraicClosure ℚ)) ((h : G F (AlgebraicClosure ℚ)) y) := rfl
    rw [e1, hκ h, map_mul, map_pow, hgζ, hκ g, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
    apply (hmod _ _).mpr
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsUnif

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_uniformizer_ord' (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : 𝓞 F, ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧
      ord ((ϖ : F) : v.adicCompletion F) = 1 := by
  have hlt : v.asIdeal ^ (1 + 1) < v.asIdeal ^ 1 := Ideal.pow_succ_lt_pow v.ne_bot 1
  rw [pow_one] at hlt
  obtain ⟨ϖ, hϖ, hϖ2⟩ := SetLike.exists_of_lt hlt
  refine ⟨ϖ, hϖ, hϖ2, ?_⟩
  apply GroundTheory.Global.ord_eq_one_of_valued_eq_exp
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hne := v.intValuation_ne_zero ϖ h0
  have h1 : v.intValuation ϖ ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation ϖ ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    hϖ2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hval : v.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h1 h2
    omega
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_of_algebraMap v ϖ).trans hval

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsInvGen

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem invMatch_gen' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : InvNormalised ζ inv)
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
     :
    ∃ (z0 : Z2 (muLoc Kf.1 l r A)) (x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2), (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x0) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z0.1 (ev (s 0), ev (s 1))).val) ∧
      inv A (Submodule.Quotient.mk z0) = 1 ∧
      gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x0) = - zmodToQZ (l ^ r) 1 := by
  have hN0 : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hU := exists_uniformizer_ord' (↥Kf.1) (v : HeightOneSpectrum (𝓞 Kf.1))
  obtain ⟨ϖ, hϖv, hϖ2, hord⟩ := hU
  have hϖ0 : (ϖ : ↥Kf.1) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ϖ = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [h']
    exact Submodule.zero_mem _
  have hy0 : ∃ y : AlgebraicClosure ℚ,
      y ^ (l ^ r) = algebraMap (↥Kf.1) (AlgebraicClosure ℚ) (ϖ : ↥Kf.1) :=
    IsAlgClosed.exists_pow_nat_eq _ hN0
  obtain ⟨y, hy⟩ := hy0
  have hK := exists_kummer' (↥Kf.1) A ζ hζ (ϖ : ↥Kf.1) hϖ0 y hy
  obtain ⟨κ, hκ, hκc, hκcoc⟩ := hK
  have hC := exists_chi' Kf (v : HeightOneSpectrum (𝓞 Kf.1)) A hA ⟨l ^ r, hN0⟩ (ιs v) ev hev
  obtain ⟨χ, hχadd, hχIne, hχFrob, hχc, hχev⟩ : ∃ χ : Dec (F := Kf.1) A → ZMod (l ^ r),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A,
        IsFrob (F := Kf.1) A (normV (v : HeightOneSpectrum (𝓞 Kf.1))) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ⟨l ^ r, hN0⟩ σ := hC
  have hF := found_side' Kf S hr hS ζ hζ ιs v A hA ev hev ϖ hord y hy κ hκ χ hχev
  obtain ⟨x0, hx0, hinv0⟩ := hF
  have hcont : Continuous (fun p : Dec (F := Kf.1) A × Dec (F := Kf.1) A => κ p.1 * χ p.2) :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ r) × ZMod (l ^ r) => q.1 * q.2)).comp
      ((hκc.comp continuous_fst).prodMk (hχc.comp continuous_snd))
  let z0 : Z2 (muLoc Kf.1 l r A) := ⟨fun p => κ p.1 * χ p.2, hcont, fun g h k => by
    show ((cycMod Kf.1 (AlgebraicClosure ℚ) l r (g : G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * (κ h * χ k) - κ (g * h) * χ k + κ g * χ (h * k) - κ g * χ h = 0
    rw [hκcoc, hχadd]
    ring⟩
  refine ⟨z0, x0, hx0, ?_, hinv0⟩
  exact (hinv A v.1 hA).2 ϖ y κ χ z0 hϖv hϖ2 hy hκ hχadd hχIne hχFrob (fun g h => rfl)

end PositivityTheory.Lit1.PTN
end
end
end
