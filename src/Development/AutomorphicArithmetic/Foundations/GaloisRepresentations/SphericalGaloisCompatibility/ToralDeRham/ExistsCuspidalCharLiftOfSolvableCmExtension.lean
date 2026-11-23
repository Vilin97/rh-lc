module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosedStatement
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwistStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  first | (exact @GlobalTheory.DegOneChar.exists_charLift) | (exact GlobalTheory.DegOneChar.exists_charLift) | (intros; apply GlobalTheory.DegOneChar.exists_charLift  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SolvableAscentInduction

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.SolvUp

theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ H : Subgroup Γ, H.Normal ∧ H.index.Prime := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using H.mul_mem h1 hn⟩
  refine ⟨H, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ H)) (mt Subgroup.index_eq_one.1 hH.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' H) = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
      have hx : x ∈ H := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective H) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

theorem isCMField_of_ringEquiv {A B : Type} [Field A] [NumberField A] [Field B] [NumberField B] [IsCMField A]
    (e : A ≃+* B) : IsCMField B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex B := isTotallyComplex_of_algebra A B
  letI : Algebra (maximalRealSubfield A) B :=
    ((e : A →+* B).comp (algebraMap (maximalRealSubfield A) A)).toAlgebra
  let f : A ≃ₐ[maximalRealSubfield A] B := { e with commutes' := fun _ => rfl }
  haveI : Module.Free (maximalRealSubfield A) B := Module.Free.of_equiv f.toLinearEquiv
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield A) B :=
    ⟨by rw [← f.toLinearEquiv.finrank_eq]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield A) B

end GlobalTheory.SolvUp

namespace GlobalTheory.SolvUp

theorem isCMField_intermediate (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [Algebra K M]
    [IsScalarTower K M Ω] (L : IntermediateField K M) : IsCMField L := by
  let f := IsScalarTower.toAlgHom K M Ω
  haveI : NumberField f.fieldRange := NumberField.of_ringEquiv M _ (AlgEquiv.ofInjectiveField f).toRingEquiv
  haveI : NumberField (L.map f) := NumberField.of_ringEquiv L _ (IntermediateField.equivMap L f).toRingEquiv
  haveI : IsCMField f.fieldRange := isCMField_of_ringEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv
  have hle : L.map f ≤ f.fieldRange := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map L).1 hy
    exact AlgHom.mem_fieldRange.2 ⟨x, rfl⟩
  haveI : IsCMField (L.map f) := (GlobalTheory.T.cm_subfields_compositum_closed Ω K).2.1 f.fieldRange (L.map f) hle inferInstance
  exact isCMField_of_ringEquiv (IntermediateField.equivMap L f).symm.toRingEquiv

end GlobalTheory.SolvUp
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ExistsCuspidalCharLiftOfSolvableCmExtension

section

@[expose] public section

namespace GalTw

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem isWeaklyAttached_of_cmBaseChange_of_finrank (hI : UpperTheory.Gal.ToralGalois.Inq) (Ω : Type) [Field Ω] (M : Type) [Field M] [NumberField M] [IsCMField M]
    [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (d : ℕ) :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra K M]
      [IsScalarTower K M Ω], Module.finrank K M = d → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)),
      InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω),
      (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N →
      ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K _ _ _ _ _ _ _ hd π χ hsc r hr N hN hS
  obtain ⟨hgal, hsol, hdec⟩ := hS
  by_cases h1 : Module.finrank K M = 1
  · obtain ⟨P, hP⟩ := GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne K M h1 a ha π
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K M l a ha π χ P hP.1 hsc
    exact ⟨P, χ', hχ', hP⟩
  haveI : Group.IsSolvable (M ≃ₐ[K] M) := hsol
  haveI : Nontrivial (M ≃ₐ[K] M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := K) (M := M)
    omega
  obtain ⟨H, hH, hp⟩ := GlobalTheory.SolvUp.exists_normal_prime_index (M ≃ₐ[K] M)
  let K₁ := IntermediateField.fixedField H
  haveI : IsGalois K K₁ := IsGalois.of_fixedField_normal_subgroup H
  haveI : IsCMField K₁ := GlobalTheory.SolvUp.isCMField_intermediate Ω K M K₁
  haveI : Module.IsTorsionFree K₁ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K₁ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) K₁⟩
  haveI : Group.IsSolvable (M ≃ₐ[K₁] M) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom K) (AlgEquiv.restrictScalars_injective K)
  have hdeg : Module.finrank K K₁ = H.index := by
    have h2 := Module.finrank_mul_finrank K K₁ M
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M, ← H.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hp₁ : (Module.finrank K K₁).Prime := hdeg ▸ hp
  have hlt : Module.finrank K₁ M < d := by
    rw [← hd, ← Module.finrank_mul_finrank K K₁ M, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt

  have hmove : ∃ g : G K Ω, (∃ x : K₁, g (algebraMap K₁ Ω x) ≠ algebraMap K₁ Ω x) ∧ (r g).val.trace ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x : K₁, x ∉ Set.range (algebraMap K K₁) := by
      by_contra hc
      push_neg at hc
      have hb : Function.Bijective (algebraMap K K₁) := ⟨(algebraMap K K₁).injective, fun y => hc y⟩
      exact hp.one_lt.ne' (hdeg ▸ Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb)
    by_contra hc
    push_neg at hc
    have hfixN : ∀ n ∈ N, n (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro n hn
      by_contra hne
      exact hN n hn (hc n ⟨x, hne⟩)
    have hfix : ∀ g : G K Ω, g (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro g
      obtain ⟨z, n, hn, rfl⟩ := hdec g
      have hz : algebraMap K₁ Ω x = algebraMap M Ω (x : M) := IsScalarTower.algebraMap_apply K₁ M Ω x
      show z (n (algebraMap K₁ Ω x)) = _
      rw [hfixN n hn, hz]
      exact z.commutes _
    have hmem : algebraMap K₁ Ω x ∈ (⊥ : IntermediateField K Ω) := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω), IntermediateField.fixingSubgroup_bot,
        IntermediateField.mem_fixedField_iff]
      intro g _
      exact hfix g
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hmem
    apply hx
    refine ⟨k, (algebraMap K₁ Ω).injective ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply]

  have hnotw : ∀ η : HChar K, UpperTheory.V.Published.IsNormChar K₁ η → ¬ UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η := by
    intro η hη hst
    obtain ⟨g, hgM, htr⟩ := hmove
    exact htr (GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist Ω K K₁ hp₁ l ι a π r hr η hη hst g hgM)
  obtain ⟨P₁, hP₁⟩ := hI.ac K K₁ hp₁ a ha π hnotw
  have hc₁ : CharLift π P₁ := hI.chl K K₁ hp₁ a ha π P₁ hP₁
  obtain ⟨⟨χ₁, hχ₁⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K K₁ l a ha π χ P₁ hP₁ hsc
  have hr₁ : Weak P₁ ι (resTo K₁ r) := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict K K₁ Ω l ι a π P₁ hP₁ r hr
  let N₁ : Subgroup (G K₁ Ω) := N.comap (AlgEquiv.restrictScalarsHom K)
  have hS₁ : SolvDisj M N₁ := by
    refine ⟨inferInstance, ‹Group.IsSolvable (M ≃ₐ[K₁] M)›, fun g₁ => ?_⟩
    obtain ⟨z, n, hn, he⟩ := hdec (AlgEquiv.restrictScalarsHom K g₁)
    have hn₁ : ∀ y : K₁, n (algebraMap K₁ Ω y) = algebraMap K₁ Ω y := by
      intro y
      have hy : algebraMap K₁ Ω y = algebraMap M Ω (y : M) := IsScalarTower.algebraMap_apply K₁ M Ω y
      have h3 := DFunLike.congr_fun he (algebraMap K₁ Ω y)
      change g₁ (algebraMap K₁ Ω y) = z (n (algebraMap K₁ Ω y)) at h3
      rw [g₁.commutes] at h3
      apply z.injective
      rw [← h3, hy]
      exact (z.commutes _).symm
    let n₁ : G K₁ Ω := AlgEquiv.ofRingEquiv (f := n.toRingEquiv) hn₁
    refine ⟨z, n₁, ?_, ?_⟩
    · show AlgEquiv.restrictScalarsHom K n₁ ∈ N
      convert hn using 1
      ext w
      rfl
    · ext w
      have h3 := DFunLike.congr_fun he w
      exact h3
  obtain ⟨P, χ', hsc', hc'⟩ := ih _ hlt K₁ rfl P₁ χ₁ hχ₁ (resTo K₁ r) hr₁ N₁ (fun n hn => hN _ hn) hS₁
  exact ⟨P, χ', hsc', GlobalTheory.T.cuspRep_characterSupportLift_trans_tower K K₁ M a π P₁ P hc₁ hc'⟩

theorem upWeak : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  intro hI Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ l _ ι a ha π χ hsc r hr N hN hS
  exact isWeaklyAttached_of_cmBaseChange_of_finrank hI Ω M l ι a ha _ K rfl π χ hsc r hr N hN hS

end GlobalTheory.RoadU

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  first | (exact @GlobalTheory.RoadU.upWeak) | (exact GlobalTheory.RoadU.upWeak) | (intros; apply GlobalTheory.RoadU.upWeak  <;> assumption)

end
end
end GalTw
end
end
