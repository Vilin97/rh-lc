module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacMultiProdOfSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SrEasy
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SrMult
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SrPerm

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SegTwo : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → Concl σ.ρ 2

end PositivityTheory.Pf1.SegRepC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.ExistsUniqueIrredSub

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace PositivityTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end PositivityTheory.Pf1.SegRepC.Uniq

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacOfLe

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end PositivityTheory.Pf1.SegRepC.PiLocalization₂

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.JhMultRevJacSub

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Zc
open PositivityTheory.Pf1.SegRepC.SegTwo

namespace PositivityTheory.RgGu.SRC

namespace SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {N : ℕ} {v w : Fin 2 → IrrGL (k := k)} (h : v = w) (hv : ∑ a, (v a).1 = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ (GL (Fin N) k) W} (f : ω.IntertwiningMap (prodIrr v hv)) :
    ∃ (hw : ∑ a, (w a).1 = N) (f' : ω.IntertwiningMap (prodIrr w hw)),
      (Function.Injective f → Function.Injective f') ∧ (Function.Surjective f' → Function.Surjective f) := by
  subst h
  exact ⟨hv, f, id, id⟩

theorem jmc {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

end SrRev

open SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem jhMult_rev_jac_sub (hG : GeometricLemma) (hR : RhoNuRhoReducible) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    (hS : S.toRepresentation.IsIrreducible)
    (h1 : jhMult (piTensor (segTerm σ.ρ 2)) (jac (consecBlocks 2 d) S.toRepresentation) = 1) :
    jhMult (revTensor σ) (jac (consecBlocks 2 d) S.toRepresentation) = 0 := by
  by_contra h2
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  let x : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr
  have hx : x.IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  let u : Fin 2 → IrrGL (k := k) := fun a => x.nu ((a : ℕ) : ℂ)
  have hu1 : ∀ a, (u a).1 = d := fun _ => rfl
  have hu : ∑ a, (u a).1 = 2 * d := by simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hu' : ∑ a, (u (Fin.rev a)).1 = 2 * d := by
    simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have he : stdBlocks (fun a => (u a).1) hu = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  have he' : stdBlocks (fun a => (u (Fin.rev a)).1) hu' = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  let φ : ∀ a, (segTerm σ.ρ 2 a).Equiv (u a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  have Φ : (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).Equiv (prodIrr u hu) := by
    unfold prodIrr
    rw [he]
    exact multiProdEquiv (consecBlocks 2 d) φ
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f : S.toRepresentation.IntertwiningMap (prodIrr u hu) := Φ.toIntertwiningMap.comp ι
  have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp Subtype.val_injective
  have j1 : 1 ≤ jm u hu S.toRepresentation := by
    have : jm u hu S.toRepresentation = 1 := by
      unfold jm
      rw [he]
      exact (jhMult_congr_left (piTensorEquiv φ) _).symm.trans h1
    rw [this]
  have j2 : 1 ≤ jm (fun a => u (Fin.rev a)) hu' S.toRepresentation := by
    have : jm (fun a => u (Fin.rev a)) hu' S.toRepresentation ≠ 0 := by
      unfold jm
      rw [he']
      exact fun h => h2 ((jhMult_congr_left (piTensorEquiv fun a => φ (Fin.rev a)) _).trans h)
    exact Order.one_le_iff_ne_zero.2 this
  have hux : u = ![x, x.nu 1] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  have hux' : (fun a => u (Fin.rev a)) = ![x.nu 1, x] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  obtain ⟨hw, f', hf', hs'⟩ := transfer hux hu f
  have hw' : ∑ a, (![x.nu 1, x] a).1 = 2 * d := by rw [← hux']; exact hu'
  have hnx : x ≠ x.nu 1 := by
    intro h
    have h0 : x.nu ((0 : ℕ) : ℂ) = x.nu ((1 : ℕ) : ℂ) := by simpa using h
    exact absurd ((GlobalTheory.LocGL.IrrGL.nu_natCast_inj hd).1 h0) (by decide)
  have hsurj := GlobalTheory.CompanionTheory.CuspPairSub.surjective_of_jm hA hx (hx.nu 1) hnx hw hw' f' (hf' hf)
    (by rw [← jmc hux hu hw]; exact j1) (by rw [← jmc hux' hu' hw']; exact j2)
  have hsf := hs' hsurj
  have hι : Function.Surjective ι := by
    intro v
    obtain ⟨w, hw⟩ := hsf (Φ v)
    exact ⟨w, Φ.toLinearEquiv.injective hw⟩
  have htop : S = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨w, rfl⟩ := hι v
    exact w.2
  subst htop
  exact hR k d hd σ hσ (GlobalTheory.Parabolic.isIrreducible_of_equiv (topEquiv _) hS)

end PositivityTheory.RgGu.SRC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegRepOf

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel
open PositivityTheory.Pf1.SegRepC PositivityTheory.Pf1.SegRepC.SegTwo

namespace PositivityTheory.RgGu.SRC


set_option synthInstance.maxHeartbeats 400000 in
def StageP : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GeometricLemma → PositivityTheory.Pf1.SegRepC.SegTwo → ∀ {d l : ℕ}, 0 < d → 0 < l → ∀ (σ : IrrRep (GL (Fin d) k)),
    IsCuspidal σ.ρ → ∀ (i : ℕ) (hi : i + 1 < l),
    ∃ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), T.toSubmodule ≠ ⊥ ∧
      ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X),
        π.IsIrreducible → IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) →
        ∀ (w : Equiv.Perm (Fin l)), π.Equiv (piTensor fun a => segTerm σ.ρ l (w a)) →
        w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segTwo_of (hG : GeometricLemma) (hR : RhoNuRhoReducible) : PositivityTheory.Pf1.SegRepC.SegTwo := by
  intro k _ _ _ _ d hd σ hσ
  have h2 : (0 : ℕ) < 2 := by decide
  obtain ⟨S, hS, hU, h1⟩ := Uniq.exists_unique_irred_sub hd h2 σ hσ (SRC.jhMult_jac_multiProd hG hd h2 σ hσ)
  refine ⟨S, hS, hU, ?_⟩
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _ (SRC.isIrreducible_segTensor hd σ) (SRC.hasFiniteLength_jac_sub hd σ hσ S) h1 fun X _ _ ρ hρ hs => ?_
  rcases SRC.constituents_jac_sub hG hd σ hσ S ρ hρ hs with h | h'
  · exact h
  · obtain ⟨φ⟩ := h'
    exfalso
    refine jhMult_ne_zero_iff.2 ?_ (SRC.jhMult_rev_jac_sub hG hR hd σ hσ S hS h1)
    exact (IsSubquotient.of_surjective φ.toIntertwiningMap fun w => ⟨φ.symm w, φ.apply_symm_apply w⟩).trans hs

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segRep_of (hT : StageP) (hG : GeometricLemma) (h2 : PositivityTheory.Pf1.SegRepC.SegTwo) : SegmentRepresentation := by
  intro k _ _ _ _ d l hd hl σ hσ
  obtain ⟨S, hS, huniq, h1⟩ := Uniq.exists_unique_irred_sub hd hl σ hσ (SRC.jhMult_jac_multiProd hG hd hl σ hσ)
  refine ⟨S, hS, huniq, ?_⟩
  have hfl : HasFiniteLength (jac (consecBlocks l d) S.toRepresentation) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks l d) _ S.toRepresentation
      (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (Lift.isSmooth_multiProd_segTerm σ l) S) (hasFiniteLength_of_isIrreducible hS)
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _
    (PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l) hfl h1 fun X _ _ π hπ h => ?_
  obtain ⟨w, ⟨φ⟩⟩ := SRC.exists_perm_of_isSubquotient_jac hG hd hl σ hσ π hπ (Lift.isSubquotient_jac_multiProd_of_sub σ S h)
  obtain rfl : w = 1 := Lift.perm_eq_one_of_lt_succ w fun i hi => by
    obtain ⟨T, hT0, hTw⟩ := hT k hG h2 hd hl σ hσ i hi
    obtain ⟨S', hS', hle⟩ := SRC.exists_irred_le hd hl σ hσ T hT0
    obtain rfl := huniq S' hS'
    exact hTw π hπ (PiLocalization₂.isSubquotient_jac_of_le σ hle h) w φ
  exact ⟨φ⟩

end PositivityTheory.RgGu.SRC

end
end
end
