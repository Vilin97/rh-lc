module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.BciOfAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FinalAllB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PJEigB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.AdmProd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.CandParts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.IsoInv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.LevOpen
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.PreEquivSymm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocIso
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocUniq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictProd

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.InfsEqOfStrict

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isoV_map_mulChi {N : ℕ} {V V' : Submodule ℂ (Sm E N)} (χ : HChar E) (h : IsoV V V') :
    IsoV (V.map (mulChi N χ).toLinearMap) (V'.map (mulChi N χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := h
  let S : V ≃ₗ[ℂ] V.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V
  let S' : V' ≃ₗ[ℂ] V'.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V'
  refine ⟨(S.symm.trans T).trans S', fun o φ ψ hψ => ?_⟩
  obtain ⟨φ, rfl⟩ := S.surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective ψ
  have h1 : ψ.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 + opAdd χ o • φ.1 := by
    apply (mulChi N χ).injective
    rw [← act_mulChi]
    exact hψ
  have hm : act o φ.1 ∈ V := by
    have h2 : ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 ∈ V := by
      have h3 := V.sub_mem ψ.2 (V.smul_mem (opAdd χ o) φ.2)
      rwa [h1, add_sub_cancel_right] at h3
    exact (Submodule.smul_mem_iff _ (Units.ne_zero _)).1 h2
  let φo : V := ⟨act o φ.1, hm⟩
  have hψ' : ψ = ((opMul χ o : ℂˣ) : ℂ) • φo + opAdd χ o • φ := Subtype.ext h1
  rw [hψ']
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add (f := _), map_smul]
  change ((opMul χ o : ℂˣ) : ℂ) • mulChi N χ (T φo).1 + opAdd χ o • mulChi N χ (T φ).1 = act o (mulChi N χ (T φ).1)
  rw [act_mulChi, ← hT o φ φo rfl, map_add (f := _), map_smul, map_smul]

theorem sIso_twPart (χ : HChar E) {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨M, V⟩ := x
  obtain ⟨M', V'⟩ := y
  obtain ⟨h1, h2⟩ := h
  cases h1
  exact ⟨rfl, isoV_map_mulChi χ h2⟩

def R (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ) : Prop :=
  HasInfCharGL x.2 τ m ∧ x.2 ≠ ⊥

def infs {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List (Multiset ℂ) := List.ofFn fun i => P.m i τ

theorem forall₂_R {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List.Forall₂ (R τ) (parts P) (infs P τ) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [parts, infs], fun i h₁ h₂ => ?_⟩
  have hi : i < P.c := by simpa [infs] using h₂
  have key : ∀ (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ), x = ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ →
      m = P.m ⟨i, hi⟩ τ → R τ x m := by
    rintro x m rfl rfl
    exact ⟨P.inf _ τ, (P.discrete _).ne_bot⟩
  exact key _ _ (by simp [parts]) (by simp [infs])

theorem R_twPart (χ : HChar E) {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {m : Multiset ℂ} (h : R τ x m) :
    R τ (twPart χ x) (m.map (· + expo χ τ)) := by
  obtain ⟨M, V⟩ := x
  refine ⟨GlobalTheory.BCT.TwistDisc.hasInfCharGL_map h.1 χ, fun h0 => h.2 ?_⟩
  exact (Submodule.map_eq_bot_iff (e := mulChi M χ)).1 h0

theorem eq_of_forall₂ {τ : E →+* ℂ} : ∀ {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l₁ l₂ : List (Multiset ℂ)},
    List.Forall₂ (R τ) l l₁ → List.Forall₂ (R τ) l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [LemDd.InfUniq_holds E _ _ τ _ _ h₁.2 h₁.1 h₂.1, eq_of_forall₂ t₁ t₂]

theorem infs_eq_of_strict {n : ℕ} {P P' : Pre E n} (h : Strict P P') (τ : E →+* ℂ) : infs P τ = infs P' τ := by
  obtain ⟨-, hc, hm⟩ := h
  unfold infs
  rw [List.ofFn_congr hc]
  congr 1
  funext i
  rw [hm]
  rfl

end PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  have hF : List.Forall₂ SIso (parts D) (parts D') := by
    rw [hJ, hJ']
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_twPart χ₂ h))
  have hc : D.c = D'.c := by
    have := hF.length_eq
    simpa [parts] using this
  refine ⟨hF, hc, fun i => ?_⟩
  funext τ
  have hI : ∀ {Q : Pre E a} {S : Pre E b} {Z : Pre E n}, IsJoin χ₁ χ₂ Q S Z →
      infs Z τ = (infs Q τ).map (fun m => m.map (· + expo χ₁ τ)) ++ (infs S τ).map (fun m => m.map (· + expo χ₂ τ)) := by
    intro Q S Z hZ
    refine eq_of_forall₂ (forall₂_R Z τ) ?_
    rw [hZ]
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R Q τ).imp fun _ _ h => R_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R S τ).imp fun _ _ h => R_twPart χ₂ h))
  have e : infs D τ = infs D' τ := by
    rw [hI hJ, hI hJ', infs_eq_of_strict ha, infs_eq_of_strict hb]
  unfold infs at e
  rw [List.ofFn_congr hc.symm (fun j => D'.m j τ)] at e
  have := congrFun (List.ofFn_injective e) i
  simpa using this

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictEqv

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictEquivalence

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem siso_symm (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hx : _root_.GlobalTheory.CuspRep.IsStable x.2) (h : SIso x y) : SIso y x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := h
  simp only at h
  subst h
  exact ⟨rfl, F5.Bo.isoV_symm' hx hI⟩

theorem siso_trans (x y z : Σ M : ℕ, Submodule ℂ (Sm E M)) (h : SIso x y) (h' : SIso y z) : SIso x z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h, hI⟩ := h
  obtain ⟨h', hI'⟩ := h'
  simp only at h h'
  subst h h'
  exact ⟨rfl, F5.Bo.isoV_trans' hI hI'⟩

theorem forall₂_flip_of {α : Type} {R S : α → α → Prop} {p : α → Prop} (hRS : ∀ x y, p x → R x y → S y x) :
    ∀ {l l' : List α}, (∀ x ∈ l, p x) → List.Forall₂ R l l' → List.Forall₂ S l' l
  | _, _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, hp, List.Forall₂.cons hab htl =>
      List.Forall₂.cons (hRS _ _ (hp _ (List.mem_cons_self ..)) hab)
        (forall₂_flip_of hRS (fun x hx => hp x (List.mem_cons_of_mem _ hx)) htl)

theorem forall₂_trans_of {α : Type} {R : α → α → Prop} (hR : ∀ x y z, R x y → R y z → R x z) :
    ∀ {l l' l'' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l'' → List.Forall₂ R l l''
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons hab htl, List.Forall₂.cons hbc htl' =>
      List.Forall₂.cons (hR _ _ _ hab hbc) (forall₂_trans_of hR htl htl')

theorem parts_stable {n : ℕ} (P : Pre E n) : ∀ x ∈ parts P, _root_.GlobalTheory.CuspRep.IsStable x.2 := by
  intro x hx
  rw [parts, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (P.discrete i).stable

end StrictEquivalence

open StrictEquivalence in
theorem StrictEqv_holds : StrictEqv := by
  intro E _ _ _ n P P' P''
  refine ⟨fun ⟨hF, hc, hm⟩ => ⟨forall₂_flip_of (p := fun x => _root_.GlobalTheory.CuspRep.IsStable x.2) (fun x y hx h => siso_symm x y hx h)
      (parts_stable P) hF, hc.symm, fun i => ?_⟩, fun ⟨hF, hc, hm⟩ ⟨hF', hc', hm'⟩ =>
      ⟨forall₂_trans_of siso_trans hF hF', hc.trans hc', fun i => ?_⟩⟩
  · rw [hm (Fin.cast hc.symm i)]
    congr 1
  · rw [hm i, hm' (Fin.cast hc i)]
    congr 1

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictPre

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictPreorder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (hR : List.Forall₂ R (List.ofFn f) (List.ofFn g)) (i : Fin c) : R (f i) (g (Fin.cast h i)) := by
  subst h
  have := hR.get (i := i.1) (by simp) (by simp)
  simpa using this

theorem cls_eq (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hxy : SIso x y) (hy : IsDiscrete y.2)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (hσ : IsLocCompGL x.2 w σ) (hσ' : IsLocCompGL y.2 w σ') :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := hxy
  simp only at h
  subst h
  exact F5.Bo.LocUniq_holds E x1 y2 hy w σ σ' (F5.Bo.LocIso_holds E x1 x2 y2 hI w σ hσ) hσ'

end StrictPreorder

theorem StrictPre_holds : StrictPre := by
  intro E _ _ _ n P P' hS
  obtain ⟨hF, hc, hm⟩ := hS
  refine ⟨finCongr hc, fun i w => ?_, fun i τ => congrFun (hm i) τ⟩
  have hI : SIso ⟨P.N i, P.V i⟩ ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ :=
    StrictPreorder.forall₂_ofFn hc (fun j => (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)))
      (fun j => (⟨P'.N j, P'.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) hF i
  exact StrictPreorder.cls_eq _ _ hI (P'.discrete _) w (P.σ i w) (P'.σ _ w) (P.loc i w) (P'.loc _ w)

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.CandFinOfJEigFin

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.FX

theorem candFin_of_jEigFin (hJ : PositivityTheory.Rg.BcB.F.Tail.JEigFin) : CandFin :=
  Bo.candFin_of hJ Bo.Tw.FinStrict_holds Bo.StrictEqv_holds Bo.StrictPre_holds
    Bo.StrictProd_holds Bo.StrictJoin_holds Bo.CandParts_holds Bo.LevOpen_holds Bo.IsoInv_holds Bo.AdmProd_holds

end PositivityTheory.Rg.BcB.F.FX
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.BaseChangeNB

section

@[expose] public section

namespace UpperTheory.BaseChangeIdentities

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F in
theorem baseChangeNB : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  Plug2B.bci_of
    (HeckeLevelFrameExistence.frameEx_of_fin uSide (FX.candFin_of_jEigFin Tail.JB.jEigFin))
    FrameWordIdentity.frameBound FinalAllB.frameRead_holdsB

end UpperTheory.BaseChangeIdentities
end
end
