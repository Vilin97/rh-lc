module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RestrictGaloisConjugate
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.MemRangeResIff
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RangeRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SemisimpleIsoOfTraceEq
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedRepConjugationTrace

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.attached_rep_conjugation_trace : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r → AttRes π ι K r → ∀ (g : G F Ω) (s s' : G K Ω), res F Ω K s' = g * res F Ω K s * g⁻¹ → ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  first | exact @GlobalTheory.RealGal.trace_conj_of_attRes | exact GlobalTheory.RealGal.trace_conj_of_attRes | (intros; apply GlobalTheory.RealGal.trace_conj_of_attRes <;> assumption)
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedRepsAgreeOnIntersection

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.attached_reps_agree_on_intersection : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι ↥Q.K r → AttRes π ι ↥Q'.K r' → ∀ (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω), res F Ω ↥Q.K s = res F Ω ↥Q'.K s' → ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  first | exact @GlobalTheory.RealGalCompat.trace_eq | exact GlobalTheory.RealGalCompat.trace_eq | (intros; apply GlobalTheory.RealGalCompat.trace_eq <;> assumption)
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.QuadraticCmCharacterInjective

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.quadratic_cm_character_injective : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ η : QCM F Ω → (G F Ω →* ℤˣ), Function.Injective η ∧ ∀ Q, (η Q).ker = (res F Ω ↥Q.K).range ∧ IsOpen ((η Q).ker : Set (G F Ω)) := by
  first | exact @GlobalTheory.RealGal.SignChar.main | exact GlobalTheory.RealGal.SignChar.main | (intros; apply GlobalTheory.RealGal.SignChar.main <;> assumption)
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SemisimpleIsoOfTraceEq

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.semisimple_iso_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r r' : Γ →* GL (Fin n) k), IsSSRep r → IsSSRep r' → (∀ s, ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r' s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → RepIso r r' := by
  first | exact @GlobalTheory.TraceConj.main | exact GlobalTheory.TraceConj.main | (intros; apply GlobalTheory.TraceConj.main <;> assumption)
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CMPatch

theorem res_injective (F Ω E : Type) [Field F] [Field Ω] [Algebra F Ω] [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] : Function.Injective (res F Ω E) := by
  intro a b h
  ext x
  have := congrArg (fun σ : G F Ω => σ x) h
  simpa using this

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (S : Set (QCM F Ω)), S.Infinite → ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q)) → ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) ∧ RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π S hS r hr
  classical
  haveI : Infinite ↥S := hS.to_subtype
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := GlobalTheory.T.quadratic_cm_character_injective F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    haveI : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact GlobalTheory.T.attached_rep_conjugation_trace F Ω ↥Q.1.K Q.1.two l ι a π (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact GlobalTheory.T.attached_reps_agree_on_intersection F Ω Q.1 Q'.1 l ι a π (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine ⟨hres, GlobalTheory.T.semisimple_iso_of_trace_eq (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_⟩
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

end GlobalTheory.CMPatch
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.galois_rep_patching_infinite_family : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (S : Set (QCM F Ω)), S.Infinite → ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q)) → ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) ∧ RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  first | exact @GlobalTheory.CMPatch.main | exact GlobalTheory.CMPatch.main | (intros; apply GlobalTheory.CMPatch.main <;> assumption)
end
end
