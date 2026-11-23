module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfExt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasY
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelsWith
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasY
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelsExt

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ModC (R : RealDat D A Ks) : Prop :=
  R.models_HX ∧ R.models_HV ∧ R.models_jX ∧ R.models_jV ∧ R.models_νY ∧ R.models_νY' ∧ R.models_νX ∧ R.models_νV

def KerC (R : RealDat D A Ks) : Prop :=
  R.chain_ωY ∧ R.chain_ωX ∧ R.chain_vY ∧ R.chain_vX ∧ R.thP_ωP ∧ R.thP_vP

variable {R : RealDat D A Ks} {V : NewLev D N} {X : NewFam A N}

def FamC (Y : NewReal R V X) : Prop :=
  (extR R Y).grp_red_R ∧ (extR R Y).grp_red_L ∧ TieExt R Y ∧ (extR R Y).fam_roots ∧ RealDat.fam_degR (A := extA A X) ∧
    RealDat.fam_degL (A := extA A X) ∧ (extR R Y).fam_muVal



def updM (Y : NewReal R V X) (HX : type_of% Y.HX) (HV : type_of% Y.HV)
    (jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H)
    (jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H)
    (νY : type_of% Y.νY) (fdY : type_of% Y.fdY) (νX : type_of% Y.νX) (fdX : type_of% Y.fdX) (νV : type_of% Y.νV)
    (fdV : type_of% Y.fdV) : NewReal R V X :=
  { Y with
    HX := HX, HV := HV, jX := jX, jV := jV, νY := νY, fdY := fdY, νX := νX, fdX := fdX, νV := νV, fdV := fdV,
    ioX := fun _ => 0, Th := fun _ => 0, thF := fun _ _ => 0, thG := fun _ _ => 0 }



def updK (Y : NewReal R V X) (ωY : type_of% Y.ωY) (ωX : type_of% Y.ωX) (ωP : type_of% Y.ωP) (vY : type_of% Y.vY)
    (vX : type_of% Y.vX) (vP : type_of% Y.vP) : NewReal R V X :=
  { Y with ωY := ωY, ωX := ωX, ωP := ωP, vY := vY, vX := vX, vP := vP }



def updL (Y : NewReal R V X) (ioY : type_of% (extR R Y).ioY) (ioX : type_of% (extR R Y).ioX) (Th : type_of% (extR R Y).Th)
    (thF : type_of% (extR R Y).thF) (thG : type_of% (extR R Y).thG) : NewReal R V X :=
  { Y with
    ioY := fun n => ioY (.inr n), ioX := fun n => ioX (.inr n), Th := fun n => Th (.inr n),
    thF := fun i n => thF i (.inr n), thG := fun i n => thG i (.inr n) }


theorem isModels_ext (hM : R.IsModels) (Y : NewReal R V X) (h : ModC (extR R Y)) : (extR R Y).IsModels := by
  refine ⟨?_, hM.vpos, ?_, ?_, ?_, h.1, h.2.1, ?_, ?_, ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hM.inf :))
  · exact (by with_unfolding_all exact (hM.cX :))
  · exact (by with_unfolding_all exact (hM.cV :))
  · exact (by with_unfolding_all exact (hM.prX :))
  · exact (by with_unfolding_all exact (hM.HE :))
  · exact (by with_unfolding_all exact (hM.HW :))
  · exact (by with_unfolding_all exact (hM.gE :))
  · exact (by with_unfolding_all exact (hM.gW :))
  · exact (by with_unfolding_all exact (hM.ν0 :))
  · exact (by with_unfolding_all exact (hM.νW :))
  · exact (by with_unfolding_all exact (hM.BV :))
  · exact (by with_unfolding_all exact (hM.order :))


theorem isFam_ext (hF : R.IsFam) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsFam := by
  refine ⟨?_, ?_, h.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · obtain ⟨g, c, c', ht⟩ := hF.tie
    have h1 := h.2.2.1 g c c' ht
    refine ⟨g, ?_, ?_, ?_⟩
    · exact (by with_unfolding_all exact (c :))
    · exact (by with_unfolding_all exact (c' :))
    · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (hF.Sb :))
  · exact (by with_unfolding_all exact (hF.pl_onto :))
  · exact (by with_unfolding_all exact (hF.etaVal :))


theorem isGrp_ext {F : Face D A} (hG : R.IsGrp F) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsGrp (extF F X) := by
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hG.levels :))
  · exact (by with_unfolding_all exact (hG.record :))
  · exact (by with_unfolding_all exact (hG.chiW :))



theorem models_stage (hM : R.IsModels) (Y : NewReal R V X) (h : FamC Y) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') := by
  choose HX jX h1 h2 using fun n => exists_modX (extR R Y) (.inr n)
  choose HV jV h3 h4 using fun i n => exists_modV (extR R Y) i (.inr n)
  choose νY fdY h5 h6 using fun n j => exists_measY (extR R Y) (.inr n) j
  choose νX fdX h7 using fun n => exists_measX (extR R Y) (.inr n)
  choose νV fdV h8 using fun i n => exists_measV (extR R Y) hM.vpos i (.inr n)
  refine ⟨updM Y HX HV jX jV νY fdY νX fdX νV fdV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.HX t :))
    · exact (by with_unfolding_all exact (h1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.HV i t :))
    · exact (by with_unfolding_all exact (h3 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.jX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.jV i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY t :))
    · exact (by with_unfolding_all exact (h5 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY' t :))
    · exact (by with_unfolding_all exact (h6 n _ rfl :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νX t :))
    · exact (by with_unfolding_all exact (h7 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.νV i t :))
    · exact (by with_unfolding_all exact (h8 i n :))



theorem ker_stage (hc : R.IsChain) (hp : R.IsThP) (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y)
    (hm : ModC (extR R Y)) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') ∧ KerC (extR R Y') := by
  have hψ : IsStdChar D (extR R Y).ψ (-1) := (hc.ωX A.μ0).std
  choose ωY vY h1 using fun n k => exists_kerY (R := extR R Y) hL hψ (.inr n) k ((by with_unfolding_all exact (fun hk => (hc.vY A.μ0 k hk).1 :)))
  choose ωX vX h2 h3 using fun n => exists_kerX (R := extR R Y) hL hψ (.inr n) ((by with_unfolding_all exact ((hc.vX A.μ0).1 :)))
  choose ωP vP h4 h5 using fun i n => exists_kerP (R := extR R Y) hL hψ i (.inr n) ((by with_unfolding_all exact ((hp.vP i A.μ0).1 :)))
  refine ⟨updK Y ωY ωX ωP vY vX vP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · exact (by with_unfolding_all exact (hm :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).1 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).2 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vX t :))
    · exact (by with_unfolding_all exact (h3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.ωP i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.vP i t :))
    · exact (by with_unfolding_all exact (h5 i n :))


theorem isChain_updL (hc : R.IsChain) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with ioY := ioY, ioX := ioX, Th := Th } : RealDat D (extA A X) Ks).IsChain) :
    (extR R (updL Y ioY ioX Th thF thG)).IsChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωY :))
  · exact (by with_unfolding_all exact (h.ωX :))
  · exact (by with_unfolding_all exact (h.vY :))
  · exact (by with_unfolding_all exact (h.vX :))
  · exact (by with_unfolding_all exact (h.ptY :))
  · exact (by with_unfolding_all exact (h.ptX :))
  · exact (by with_unfolding_all exact (h.ItY :))
  · exact (by with_unfolding_all exact (h.ItX :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioY t :))
    · exact (by with_unfolding_all exact (h.ioY (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioX t :))
    · exact (by with_unfolding_all exact (h.ioX (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.Th t :))
    · exact (by with_unfolding_all exact (h.Th (.inr n) :))


theorem isThP_updL (hp : R.IsThP) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with thF := thF, thG := thG } : RealDat D (extA A X) Ks).IsThP) :
    (extR R (updL Y ioY ioX Th thF thG)).IsThP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωP :))
  · exact (by with_unfolding_all exact (h.vP :))
  · exact (by with_unfolding_all exact (h.pt_theta :))
  · exact (by with_unfolding_all exact (h.ioP :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF_mem i t :))
    · exact (by with_unfolding_all exact (h.thF_mem i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF i t :))
    · exact (by with_unfolding_all exact (h.thF i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thG i t :))
    · exact (by with_unfolding_all exact (h.thG i (.inr n) :))



theorem core_ext (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y) :
    ∃ Y' : NewReal R V X, GlobalTheory.Hk3.Core (extR R Y') (extF F X) ∧ TieExt R Y' := by
  obtain ⟨Y1, f1, m1⟩ := models_stage hC.models Y h
  obtain ⟨Y2, f2, m2, k2⟩ := ker_stage hC.chain hC.thP hL Y1 f1 m1
  have hF := isFam_ext hC.fam Y2 f2
  have hM := isModels_ext hC.models Y2 m2
  have e1 := GlobalTheory.ConjExt.exists_chain (R := extR R Y2) h₁ h₂ h₃ h₄ hP hL (isGrp_ext hC.grp Y2 f2).record hF hM k2.1 k2.2.1 k2.2.2.1
    k2.2.2.2.1 (.inl A.μ0) ((by with_unfolding_all exact (hC.chain.ItY A.μ0 :))) ((by with_unfolding_all exact (hC.chain.ItX A.μ0 :)))
  have e2 := GlobalTheory.ConjExt.exists_thP (R := extR R Y2) h₃ hL hF hM k2.2.2.2.2.1 k2.2.2.2.2.2 (.inl A.μ0)
    ((by with_unfolding_all exact (fun i => hC.thP.ioP i A.μ0 :)))
  obtain ⟨ioY, ioX, Th, c3⟩ := e1
  obtain ⟨thF, thG, p3⟩ := e2
  have f3 : FamC (updL Y2 ioY ioX Th thF thG) := (by with_unfolding_all exact (f2 :))
  have m3 : ModC (extR R (updL Y2 ioY ioX Th thF thG)) := (by with_unfolding_all exact (m2 :))
  exact ⟨updL Y2 ioY ioX Th thF thG, ⟨hL, isGrp_ext hC.grp _ f3, isFam_ext hC.fam _ f3, isModels_ext hC.models _ m3,
    isChain_updL hC.chain Y2 _ _ _ _ _ c3, isThP_updL hC.thP Y2 _ _ _ _ _ p3⟩, f3.2.2.1⟩

end GlobalTheory.TupExt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSideV

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

def SideLev : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {V : NewLev D N}

theorem extL_is (hL : R.toLevCh.Is A.μ0) (hV : ∀ n, TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) (hi : Function.Injective V.xiH)
    (hn : ∀ n t, V.xiH n ≠ R.xiH t)
    (hQ : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
        ∀ n, ∀ PP ∈ V.Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) :
    (extL R.toLevCh V).Is (.inl A.μ0) :=
  { mu0 := hL.mu0
    eta := hL.eta
    xi := Sum.rec hL.xi fun n => (hV n).xi
    xi_inj := by
      rintro (t | n) (t' | n') h
      · exact congrArg _ (hL.xi_inj h)
      · exact absurd h.symm (hn n' t)
      · exact absurd h (hn n t')
      · exact congrArg _ (hi h)
    xi_base := hL.xi_base
    xi_fin := Sum.rec hL.xi_fin fun n => (hV n).xi_fin
    xi_triv := Sum.rec hL.xi_triv fun n => (hV n).xi_triv
    xi_tame := Sum.rec hL.xi_tame fun n => (hV n).xi_tame
    Pg := hL.Pg
    Q_pl := Sum.rec hL.Q_pl fun n => (hV n).Q_pl
    Q_off := Sum.rec hL.Q_off fun n => (hV n).Q_off
    Q_de p hp := (hQ p hp).imp fun _ h => Sum.rec h.1 h.2
    Q_ram := Sum.rec hL.Q_ram fun n => (hV n).Q_ram
    chi := hL.chi
    xiR := Sum.rec hL.xiR fun n => (hV n).xiR
    βY := hL.βY
    βX := hL.βX
    βV := hL.βV
    βW := hL.βW }

theorem Q_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem fun PP hP => (hL.Q_ram A.μ0 PP).2 (Or.inl hP) (by
    show (R.xiH A.μ0).UnrAt PP
    rw [hL.xi_base]
    exact fun _ _ => rfl)


open Formalism.L2.Host Formalism.L2.Col GlobalTheory.RationalValues in
theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) {χ xi Q xiR} (h : TwLev R χ xi Q xiR) :
    ∀ PP ∈ Q, ∀ x, ((xiR PP x : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  intro PP hPP x
  have i : Fin D.R.m := ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩
  obtain ⟨g, c, c', ht⟩ := hF.tie
  have hok := ht.ok A.μ0
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ Q ∪ R.Q A.μ0
  have hQ : ∀ v ∈ Q, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → χ.UnrAt v := fun v hv => by
    by_contra hn
    rcases (h.Q_ram v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → χ.val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : ((χ.val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm h.xi_triv (hu v hv) hc, Units.val_one]
      show ((χ.val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hF.pl_onto v (hs _ hS)
      have h1 : (R.C.mu0 i * χ).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange := by
        obtain ⟨a, ha⟩ := h.muVal i P (hs _ fun w hw => hw.elim (hS w) (hQ w))
        exact ⟨_, ha⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hF.muVal i A.μ0 P ((hok P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := h.xi_fin
  obtain ⟨a, k, hk, hx, hm⟩ := TypeValues.exists_lift_mem χ _ (T ∪ T.image conjPrime₂) h.xi_tame
    (TypeValues.inf_eq_one _ hn ho) hu hv (Finset.mem_union_left _ (hQ PP hPP)) x
  rw [h.xiR PP hPP a k x hk hx]
  exact hm


variable (R V) in
def okOf (n : N) : Set Pl0 := {P | Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))}

theorem okOf_subset (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (n : N) : okOf R V n ⊆ A.ok A.μ0 := by
  obtain ⟨g, c, c', ht⟩ := hF.tie
  intro P hP
  refine (ht.ok A.μ0 P).2 ?_
  rw [Q_base hL, Finset.coe_empty, Set.union_empty]
  exact ⟨hP.1, fun h => hP.2.1 (Or.inl h), fun w hw => hP.2.2 w (Or.inl hw)⟩

theorem sep_new (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (n : N) : ∀ PP ∈ R.Pg, ∀ PP' ∈ V.Q n,
    PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP := fun PP h PP' h' =>
  ⟨fun e => Finset.disjoint_left.1 (idem_of_is hL' (.inr n)).1 h (e ▸ h'),
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL' (.inr n) (Or.inl h) (Or.inr h'),
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL' (.inr n) (Or.inr h') (Or.inl h)⟩



theorem exists_sideX (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (n : N)
    (hV : TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) :
    ∃ (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : okOf R V n × ℕ → Module.End D.what₂.LL S.Forms)
      (B : Bridge.SideReal D D.sp.X' (Bridge.envOf R.cX.coef
        (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (okOf R V n))) S act op (fun i => i.2)),
      (∀ q : (levEnv D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n))).Q, R.eG (B.act_tie.red q) =
        rTup R.βX ((extL R.toLevCh V).datXt (.inr n)) (Formalism.UG.bc (Lev.swapAE D) ((q : Bridge.Gf D.sp.X') : GL _ _))) ∧
      (∀ (lam : D.what₂.Tau → DomWeight D.sp.X'.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] R.cX.coef.W) pair nab del,
        Bridge.CoefTie D.sp.X' R.cX.coef (R.B.R A.μ0).pres lam c0 pair nab del → Bridge.CoefTie D.sp.X' R.cX.coef B.pres lam c0 pair nab del) ∧
      ∀ P, op (P, 0) = 1 ∧ ∀ k, D.sp.X'.rank < k → op (P, k) = 0 := by
  have hχ := GlobalTheory.RationalValues.chiVal_of_chiW R hC.grp.chiW
  have hξ := xiR_mem hC.lev hC.fam hV
  obtain ⟨g, c, c', ht⟩ := hC.fam.tie
  have key := hS D G D.sp.X' R.βX R.ΛX hC.lev.βX (R.datXt A.μ0) (V.Q n) ((extL R.toLevCh V).datXt (.inr n)).xq Pl0 R.pl (A.ok A.μ0)
    (okOf R V n) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))
    (by show R.Q A.μ0 ⊆ _; rw [Q_base hC.lev]; exact Finset.empty_subset _) (okOf_subset hC.lev hC.fam n) (sep_new hL' n)
    (fun P hP => hP) (fun PP h => h.elim (fun h => Or.inl (hC.fam.Sb h)) Or.inr)
    (fun j hj PP hP x => hχ ⟨j, hj⟩ PP hP x)
    (fun PP hP x => by
      have e : ((extL R.toLevCh V).datXt (.inr n)).xq PP x = (V.xiR n PP x)⁻¹ := rfl
      rw [e, Units.val_inv_eq_inv_val]
      exact Subfield.inv_mem _ (hξ PP hP x))
    R.cX.coef _ _ _ (R.B.R A.μ0) ⟨_, c, _, _, _, _, ht.mapR, ht.coefR A.μ0⟩
  obtain ⟨S, act, op, B, h1, h2, h3⟩ := key
  refine ⟨S, act, op, B, fun q => ?_, h2, h3⟩
  obtain ⟨hq, e⟩ := h1 q
  exact (congrArg R.eG e).trans (hC.grp.red_R A.μ0 ⟨q, hq⟩)



theorem exists_sideV (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (i : Fin D.R.m)
    (n : N) (hV : TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) :
    ∃ (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : okOf R V n × ℕ → Module.End D.what₂.LL S.Forms)
      (B : Bridge.SideReal D (Vc D i) (Bridge.envOf (R.cV i).coef
        (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (okOf R V n))) S act op (fun i => i.2)),
      (∀ q : (levEnv (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n))).Q, R.eG (B.act_tie.red q) =
        rTup (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) (Formalism.UG.bc (Lev.swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _))) ∧
      (∀ (lam : D.what₂.Tau → DomWeight (Vc D i).rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] (R.cV i).coef.W) pair nab del,
        Bridge.CoefTie (Vc D i) (R.cV i).coef (R.B.L i A.μ0).pres lam c0 pair nab del →
          Bridge.CoefTie (Vc D i) (R.cV i).coef B.pres lam c0 pair nab del) ∧
      ∀ P, op (P, 0) = 1 ∧ ∀ k, (Vc D i).rank < k → op (P, k) = 0 := by
  have hχ := GlobalTheory.RationalValues.chiVal_of_chiW R hC.grp.chiW
  have hξ := xiR_mem hC.lev hC.fam hV
  obtain ⟨g, c, c', ht⟩ := hC.fam.tie
  have key := hS D G (Vc D i) (R.βV i) (R.ΛV i) (hC.lev.βV i) (R.datVt i A.μ0) (V.Q n) ((extL R.toLevCh V).datVt i (.inr n)).xq Pl0 R.pl
    (A.ok A.μ0) (okOf R V n) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))
    (by show R.Q A.μ0 ⊆ _; rw [Q_base hC.lev]; exact Finset.empty_subset _) (okOf_subset hC.lev hC.fam n) (sep_new hL' n)
    (fun P hP => hP) (fun PP h => h.elim (fun h => Or.inl (hC.fam.Sb h)) Or.inr)
    (fun j _ PP hP x => by
      have e : (R.datVt i A.μ0).cg (j + 1) PP x = (R.chi ((i : ℕ) + 1) PP x)⁻¹ := rfl
      rw [e, Units.val_inv_eq_inv_val]
      exact Subfield.inv_mem _ (hχ i PP hP x))
    (fun PP hP x => hξ PP hP x)
    (R.cV i).coef _ _ _ (R.B.L i A.μ0) ⟨_, c' i, _, _, _, _, ht.mapL i, ht.coefL i A.μ0⟩
  obtain ⟨S, act, op, B, h1, h2, h3⟩ := key
  refine ⟨S, act, op, B, fun q => ?_, h2, h3⟩
  obtain ⟨hq, e⟩ := h1 q
  exact (congrArg R.eG e).trans (hC.grp.red_L i A.μ0 ⟨q, hq⟩)



def newRealOfSideData {X : NewFam A N}
    (BR : ∀ n, Bridge.SideReal D D.sp.X'
      (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (X.ok n)))
      (X.SR n) (X.actR n) (X.opR n) (fun i => i.2))
    (BL : ∀ i n, Bridge.SideReal D (Vc D i)
      (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (X.ok n)))
      (X.SL i n) (X.actL i n) (X.opL i n) (fun i => i.2)) : NewReal R V X where
  BR := BR
  BL := BL
  HX _ := R.HX A.μ0
  HV i _ := R.HV i A.μ0
  jX _ := 0
  jV _ _ := 0
  νY _ := R.νY A.μ0
  fdY _ := R.fdY A.μ0
  νX _ := R.νX A.μ0
  fdX _ := R.fdX A.μ0
  νV i _ := R.νV i A.μ0
  fdV i _ := R.fdV i A.μ0
  ωY _ := R.ωY A.μ0
  ωX _ := R.ωX A.μ0
  ωP i _ := R.ωP i A.μ0
  vY _ := R.vY A.μ0
  vX _ := R.vX A.μ0
  vP i _ := R.vP i A.μ0
  ioY _ _ := 0
  ioX _ := 0
  Th _ := 0
  thF _ _ := 0
  thG _ _ := 0



theorem fam_stage (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0))
    (hV : ∀ n, TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) : ∃ (X : NewFam A N) (Y : NewReal R V X), FamC Y := by
  choose SR actR opR BR a1 a2 a3 using fun n => exists_sideX hS hC hL' n (hV n)
  choose SL actL opL BL b1 b2 b3 using fun i n => exists_sideV hS hC hL' i n (hV n)
  choose mu hmu using fun i n P => exists_cond (1 : D.what₂.LLˣ) ((hV n).muVal i P)
  refine ⟨⟨okOf R V, mu, SR, actR, opR, SL, actL, opL⟩, newRealOfSideData BR BL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.grp.red_R t :))
    · exact (by with_unfolding_all exact (a1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.grp.red_L i t :))
    · exact (by with_unfolding_all exact (b1 i n :))
  · intro g c c' ht
    refine ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ?_, ht.gramR_eq, ht.mapR, ht.mapL, ?_, ?_⟩
    · rintro (t | n)
      · exact (by with_unfolding_all exact (ht.ok t :))
      · exact fun _ => Iff.rfl
    · rintro (t | n)
      · exact (by with_unfolding_all exact (ht.coefR t :))
      · exact (by with_unfolding_all exact (a2 n _ _ _ _ _ (ht.coefR A.μ0) :))
    · rintro i (t | n)
      · exact (by with_unfolding_all exact (ht.coefL i t :))
      · exact (by with_unfolding_all exact (b2 i n _ _ _ _ _ (ht.coefL i A.μ0) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.fam.roots t :))
    · exact fun PP h => h.elim (fun h => hC.fam.roots A.μ0 PP (Or.inl h)) ((hV n).roots PP)
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.fam.degR t :))
    · exact (by with_unfolding_all exact (a3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.fam.degL i t :))
    · exact (by with_unfolding_all exact (b3 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.fam.muVal i t :))
    · exact (by with_unfolding_all exact (hmu i n :))

end GlobalTheory.TupExt

end
end
end
