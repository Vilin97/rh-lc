module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStepOfFamily
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
public import Formalism.LocalToGlobal.Columns.DecoFin
import Mathlib.Data.Nat.Choose.Multinomial
public import Formalism.LocalToGlobal.Columns.CoefCol
public import Formalism.LocalToGlobal.Columns.ColForms
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundLevelPrimePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UkTermOfMoveStep
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLawsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMomentsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.kernelJets_levelPlace_integralMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments := by
  first | exact @GlobalTheory.MomTop.jetMoments | exact GlobalTheory.MomTop.jetMoments | (intros; apply GlobalTheory.MomTop.jetMoments <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZeroStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

theorem _root_.GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.VecP χ ∧ B.LatAll ∧ ∀ a b, B.ThZeroMem a b := by
  first | exact @GlobalTheory.NatFamily.family | exact GlobalTheory.NatFamily.family | (intros; apply GlobalTheory.NatFamily.family <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.Columns.AtTOwedV

section

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.IsUp.sameAt {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (h : Deco.IsUp P q d d') {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P.1) (hQ' : Q ≠ conjPrime₂ P.1) :
    SameAt Q d.N d'.N := by
  obtain ⟨x, hx, -, rfl⟩ := h
  exact (upN_spec hd.lat hd.uni P.1 hP.ne hx).2.2.1 Q hQ hQ'

theorem Deco.IsUp.f_ne {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') {Q : ST}
    (hQ : Q ≠ P) : d'.f Q = d.f Q := by
  obtain ⟨x, _, _, rfl⟩ := h
  simp only [Deco.up, Function.update, dif_neg hQ]

theorem Deco.IsUp.be_eq {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') : d'.be = d.be := by
  obtain ⟨x, _, _, rfl⟩ := h
  rfl

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.UpLaw

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop} {T : ℕ} {P : ST}
  (hP : MoveHyp ST SG P) (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
  (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : y.Off P.1)

include hP hT hQ hy

theorem above_iff (b : β) (p q : PtY ST SG Q y) : Above (tdatY ST T y β Λ Θ pref) b P p q ↔
    p.1.1.deco.1.IsUp P (T : 𝓞 X.E) q.1.1.deco.1 ∧ q.1.1.1.2 = p.1.1.1.2 ∧ q.1.2 = p.1.2 := by
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨⟨x, hx, hf, h.1⟩, h.2⟩
  · rintro ⟨⟨x, hx, hf, e⟩, h2, h3⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨x, hx, hf, PtY.ext' (Subtype.ext (e.trans h.1.symm)) (h2.trans h.2.1.symm) (h3.trans h.2.2.symm)⟩

theorem bijOn_up (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P p q} {d | p.1.1.deco.1.IsUp P (T : 𝓞 X.E) d.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b p q).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b p q).1 hq).2
    have h' := ((above_iff hP hT hQ hy b p q').1 hq').2
    exact PtY.ext' e (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  · obtain ⟨x, hx, hf, e⟩ := hd
    exact ⟨_, ⟨x, hx, hf, rfl⟩, Subtype.ext ((mv_up T p P hP hT hQ hy hx hf).1.trans e.symm)⟩

theorem bijOn_dn (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P q p} {d | d.1.IsUp P (T : 𝓞 X.E) p.1.1.deco.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b q p).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b q p).1 hq).2
    have h' := ((above_iff hP hT hQ hy b q' p).1 hq').2
    exact PtY.ext' e (h.1.symm.trans h'.1) (h.2.symm.trans h'.2)
  · have hs := fun w h1 h2 => (Deco.IsUp.sameAt d.2 hP hd (Q := w) h1 h2).localization_eq.symm
    have h := p.mv_spec d (fun w => hs w.1 (hQ w).1 (hQ w).2) (hy _ _ hs)
    refine ⟨p.mv d, (above_iff hP hT hQ hy b _ p).2 ⟨?_, h.2.1.symm, h.2.2.symm⟩, h.1⟩
    rw [h.1]
    exact hd

theorem same_of_above (b : β) {p q : PtY ST SG Q y} (h : Above (tdatY ST T y β Λ Θ pref) b P p q) :
    SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2 := by
  obtain ⟨h1, h2, h3⟩ := (above_iff hP hT hQ hy b p q).1 h
  exact ⟨fun w hw => (h1.sameAt p.1.1.deco.2 hP (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm, h1.be_eq.symm,
    funext fun w => (congrFun h2 w).symm, h3.symm⟩

end Gen

theorem kAt_uk : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → GlobalTheory.KerT.UKTerm W Ch sel mu cst A u i (i + 1) → ∀ b b' (d : (stepAt sel mu cst L Tp u i).D b) (d' : (stepAt sel mu cst L Tp u (i + 1)).D b') (P : Pr.vT u) F, (∑ᶠ d₁ ∈ {d₁ | Above (tdatAt sel mu cst L Tp u (i + 1)) b' P d' d₁}, kAt W Ch sel mu cst L A u i b b' d d₁ F) = ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (tdatAt sel mu cst L Tp u i) b P d₀ d}, kAt W Ch sel mu cst L A u i b b' d₀ d' F := by
  intro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS _ Tp A hK hU b b' d d' P F
  obtain ⟨Ξ₀, hb, -, -, -, hk⟩ := hK b b' d d'
  have hP := moveHyp_of_ok hPr u P
  have hT := T_unif hX hPr u P
  have hQ0 := T_notMem_QE sel mu u hPr hsel hS
  have hQ : ∀ w : QE sel (mu : Chr X.F X.E X.K), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun w => ne_of_T_notMem hPr u P (hQ0 w.1 w.2)
  have hy := fun j => ysAt_off (R := R) sel mu cst hPr u hQ0 j P
  have refl : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p p :=
    fun p => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have key := hU d.1.1.deco (frsF sel mu d.1.1) d'.1.1.deco (frsF sel mu d'.1.1) Ξ₀ P F hP hP hb
  refine (finsum_mem_eq_of_bijOn _ (bijOn_up hP hT hQ (hy (i + 1)) b' d') fun q hq => ?_).trans
    (key.trans (congrArg _ (finsum_mem_eq_of_bijOn _ (bijOn_dn hP hT hQ (hy i) b d) fun q hq => ?_).symm))
  · rw [hk d q (refl d) (same_of_above hP hT hQ (hy (i + 1)) b' hq)]
  · obtain ⟨h1, h2, h3, h4⟩ := same_of_above hP hT hQ (hy i) b hq
    rw [hk q d' ⟨fun w hw => (h1 w hw).symm, h2.symm, h3.symm, h4.symm⟩ (refl d')]

end GlobalTheory.LvT.Built.UpLaw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentativesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

local instance representativeDatNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE


theorem _root_.GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcoveStatement

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChains

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem moveStep_fam (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    GlobalTheory.KerT.MoveStep (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := by
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hEq := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  obtain ⟨-, hLat, hTh⟩ := GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hM := GlobalTheory.ThetaMove.moveStep_of_family I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hEq hLat
    (fun a b _ _ => hTh a b) hJa
  rw [← AmbIn.amb_eq_ambOf] at hM
  exact hM

theorem kernelCondition_at_row_family (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerUK (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P F
  exact UpLaw.kAt_uk B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi)
    (GlobalTheory.KerT.UK.ukTerm_of_moveStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) I.A u i hX hPr h.sel_ok
      (h.T_mem u) (moveStep_fam h hJ l Z u a hi)) b b' d d' P F

theorem laws_true_fam : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u, Bd.ch = tw (I.tw l l0 Z) u a ∧
      (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
        letI : NumberField Bd.E := Bd.nE
        Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
      (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
      Bd = dat I l Z u a := by
  intro B X I h hJ l l0 Z u a
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hE := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hV := (GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1
  have hth : ∀ (a : I.ι) (u : B.Word), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a)
      (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) := fun a u =>
    GlobalTheory.ChainTheta.chTh_ok_of_colIn' B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ hE hV a u
  refine ⟨dat I l Z u a, dat_ch I l l0 Z u a, fun i _ => split u a h i, sees l Z u a, fun i hi => ?_, rfl⟩
  change i < B.R.m at hi
  have hKerEq : Dat.KerEq (B := dat I l Z u a) (i := i)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
    obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
    refine ⟨fun b b' g g' d d' => ?_,
      GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives B X I h hJ l Z hV u a i hi⟩
    rcases lt_trichotomy (i + 2) B.R.m with hlt | heq | hgt
    · exact GlobalTheory.MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) hlt b b' g g' d d'
    · exact GlobalTheory.CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) heq b b' g g' d d'
    · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) (by omega) b b' g g' d d'
  exact ⟨_, hKerEq, kerDil h l Z u a hi,
    kernelCondition_at_row_family h hJ l Z u a hi, GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi,
    GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi⟩

end GlobalTheory.LvT.Built.TrueLaws
end
end
end
