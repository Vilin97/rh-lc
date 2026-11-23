module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsExtGeometryTupleOfRepresentativesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitRepsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCoset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExpStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QTw.StepChar

open Formalism.L2.Col Formalism.L2.DIV
open Formalism.L2.Host (HChar)

theorem locK_unif {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q :=
  χ.val_eq hu _ ((Formalism.UG.P.levelaf_valued_algebraMap Q (k : L)).trans hk)

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem g_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (k : Fin 2) : ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)

theorem res_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (hx : (x : X.E) = (y : X.E))
    (hc : (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y) :
    σ ((resChar (mu : Chr X.F X.E X.K) P.1 c : X.Kˣ) : X.K) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ) := by
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hu : P.1.valuation X.E (x : X.E) = 1 := by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  have e1 : (m0 j * ξ).locK P.1 x = (m0 j).locK P.1 x * ξ.locK P.1 x := rfl
  rw [e1, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ (g_notMem hX hPr hsel hg P hP)) hu, one_mul,
    GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm]

theorem map_muAt (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : cst.muq (j.1 + 1) P = (((Ch.muVal j P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) (a : X.Eˣ) :
    σ (muAt Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.TwistVal.main X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hg' := g_notMem hX hPr hsel hg P hP
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  rw [← hm]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · have e1 : (m0 j * ξ).locK P.1 q = (m0 j).locK P.1 q * ξ.locK P.1 q := rfl
    rw [hm, e1, Units.val_mul, ← hq q hq', hQ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul,
      map_inv₀, map_inv₀, ht.muVal j P.1 hg', ← locK_unif (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
        (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2), mul_inv]
    rfl
  · rw [hm, if_neg hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, res_eq hX hPr hsel hg ht h j P hP x y c hx hc]

end General

theorem comp_eq_muAt_and_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  intro B X I hI l Z a P hP k _ _ _ _ q hq hint hden i hi χ hχ μ hμ
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hμ' : (ofSplit q).IsComp χ μ⁻¹ := fun x b hb => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hμ x b hb, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  constructor
  · intro x u hu
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA (I.rec7 l Z))).map_zero)
    have h1 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q hq hχ hx0 u hu
    have h2 := map_muAt hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP
      ((hI.idx_ok a).muqQ i hi P hP) (Units.mk0 x hx0)
    have h3 := hμ u (GlobalTheory.LocMod.SplitHecke.idlU q u) rfl
    rw [MonoidHom.inv_apply, Circle.coe_inv, h1] at h3
    exact h3.trans h2.symm
  · have hr : IsRes (D := I.rec7 l Z) (I.C.mu0 ⟨i, hi⟩ * I.xi a) P.1
        ((Units.map (B.embLL : B.fields.K →* ℂ)).comp (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) P.1)) :=
      fun y x c hx hc => Units.ext (res_eq hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP x y c hx hc)
    have ht := (GlobalTheory.LocMod.SplitHecke.tame_and_res (I.rec7 l Z) k q P.1 hq hint hden χ _ _ μ⁻¹ hχ hr hμ').1
    intro x hx
    have := ht x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this

end GlobalTheory.QTw.StepChar

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTameStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.step_inverse_character_local_component_chain_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  first | exact @GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | exact GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | (intros; apply GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCosetStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  first | exact @GlobalTheory.TwBridge.idxProd_twIdx | exact GlobalTheory.TwBridge.idxProd_twIdx | (intros; apply GlobalTheory.TwBridge.idxProd_twIdx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowJoin

open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem idxProd (hI : I.Ok) (hT : I.IsTw) (a : I.ι) : IdxProd I.sel (I.tup a) (I.cst a) (I.idx a) := by
  have h := hI.idx_ok a
  rw [(hT a).2] at h ⊢
  exact GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset _ _ _ _ _ _ _ _ _ _ h

theorem h_one (hT : I.IsTw) (a : I.ι) : ∀ j b (P : BadPr I a), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1 := by
  rw [(hT a).2]
  exact Formalism.L2.Col.twSt_h_g I.Ch I.sel (I.tup a) (I.cst a) _

theorem get_bij {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} (hA : A.Is) (j : ℕ) (hj : j + 1 < B.R.m) :
    Function.Bijective fun β : Ch₀ j => (A.b0 j β).get (by omega) := by
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = fun _ => ∅ := fun p => by
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj.ne] at h
    funext P
    rw [cosetIn, show p.1.2 = ∅ from h]
    simp
  refine ⟨fun β β' e => hA.chart_ext j (by omega) β β' ?_ ((h0 _).trans (h0 _).symm), fun b => ?_⟩
  · rw [← (A.b0 j β).of_get (by omega) (by omega), ← (A.b0 j β').of_get (by omega) (by omega)]
    exact congrArg (Idx.of · _) e
  · haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
    letI := B.fields.starE
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := j) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    refine ⟨A.chOf j ((I.stp u a j).cl (Idx.of b (by omega)) p), ?_⟩
    exact Idx.get_eq (congrArg Subtype.val (hA.rep j (by omega) _).1.symm) _

section Place

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}

structure Good (P : BadPr I a) (G : QGeo v Bs PP) {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk)
    (sg : ℂ) : Prop where
  sign : sg = 1 ∨ sg = -1
  tw : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  up : ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j))
  rat : ∀ j d h, Nonempty ((I.idx a).β j) → E.A j d h =
    {g | ∃ b, IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z))) ((I.idx a).h j b P) g}
  next : ∀ j d (h : j + 1 + d = G.s), Nonempty ((I.idx a).β j) → (E.A (j + 1) d h).Nonempty →
    ∃ γ : Formalism.L2.Col.AutY B.fields B.R (j + 1), Bdd (B.primes X) (j + 1) P.1 γ ∧
      ∃ al, Formalism.L2.Col.FiniteSumNonzeroLargeDepth I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j al P) γ



theorem exists_good (hI : I.Ok) (hT : I.IsTw) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs) (G : QGeo v Bs PP) (heq : PP = P.1) (hc : c.Is)
    (hstd : IsStdChar (I.rec7 l Z) c.ψ (-1)) (χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle)
    (hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (χ j) (I.C.mu0 ⟨j, hj⟩ * I.xi a)) :
    ∃ (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ), Good P G E hψ sg := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hcp : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ := heq ▸ G.compl
  have hid : Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) G.q.e P.1 := heq ▸ G.idem
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split (I.rec7 l Z) G.k (ofSplit G.q) c.ψ hstd
  choose μ hμ using fun j => hcomp (χ (j - 1))⁻¹
  have hψ := continuous_of_cond G.cond
  have hd := TC.degOne_of_ok hI a P
  obtain ⟨⟨ϖ, unif, ψ, cont, cond, δ, tame, η, unr, sg⟩, hA, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_completionTwistData_chainColumns _ _ _ _ _ _ _ _ _ _ _ hL P hP G.k (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ hcp G.unif G.ψk hψ G.cond
      (GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp (I.rec7 l Z) G.k G.q P.1 hid hd.1 hd.2 hcp.int c.ψ hstd G.ψk G.char) μ
      fun i hi => GlobalTheory.T.step_inverse_character_local_component_chain_tame I hI l Z a P hP G.k G.q hid hcp.int hcp.dense i hi (χ i) (hχ i hi) _ (hμ (i + 1))
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  have hM : G.s + 1 ≤ (I.cst a).M := by
    rw [hT.cst_eq]
    show _ ≤ B.R.m
    omega
  obtain ⟨A, a1, a2, a3, a4⟩ := exists_system G.unitVol hA hL (idxProd hI hT a) hM
  have hmu : ∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ) := fun j hj => by
    rw [h3 j (by omega)]
    exact hμ (j + 1)
  obtain ⟨E₀, rfl, rfl, rfl, e4⟩ := GlobalTheory.T.exists_extGeometry_tuple_of_representatives _ c v Bs _ G χ hc δ tame η unr hmu A a1 _ a2
  obtain ⟨E, e1, e2, e3, e5, -, e6⟩ := GlobalTheory.T.exists_splitPlaceGeometryExtension_cosetOrbitReps _ c v Bs _ G χ hc _ tame _ unr hmu _ a1 _ a2 (E₀.Ch (G.s + 1))
    (fun y => (E₀.cos y).out ∘ id) (fun y y' h => E₀.cos_inj y y' (by
      rw [← e4] at h
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using h))
    (fun z hz => by
      rw [← e4] at hz ⊢
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using E₀.cos_all z hz)
  refine ⟨E, hψ, sg, h4, ?_, e5, e6, e3 ▸ a3, e3 ▸ a4⟩
  have e7 : E.tw hψ sg = ⟨G.ϖ, unif, G.ψk, cont, cond, E₀.δ, tame, E₀.η, unr, sg⟩ := by simp only [QExt.tw, e1, e2]
  rw [e7]
  exact hA

theorem res_of_tw (hI : I.Ok) {hP : PP ∈ Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)} {G : QGeo v Bs PP} {W : TwData G.k}
    (h : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL ⟨PP, hP⟩ (G.q.pr.comp (incA (I.rec7 l Z))) G.s W)
    {ξ : (kP PP)ˣ →* ℂˣ} (hξ : IsRes (I.xi a) PP ξ) : G.Res W.δ ξ := by
  intro z x r hx hr
  have h0 : (z : (I.rec7 l Z).host.E) ≠ 0 := fun e => x.ne_zero (by rw [hx, e]; exact (G.q.pr.comp (incA (I.rec7 l Z))).map_zero)
  have h1 : Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E) = (r : kP PP) := (Formalism.L2.Col.reduction_coe PP z).trans hr.symm
  have h2 : IsUnit (Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E)) := h1 ▸ r.isUnit
  have h3 : Formalism.L2.Col.IntAt PP (z : (I.rec7 l Z).host.E) :=
    ⟨z, 1, fun e => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 e), by simp⟩
  have h4 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads a)
    (GlobalTheory.Mem.ReadTwist.tameAt (hI.xi_reads a) fun v => Subgroup.mem_iInf.1 (I.tup a).2.1.2 v) PP h2.unit z (Units.mk0 _ h0) rfl
    (hr.symm.trans h1.symm)
  refine Units.ext ((h.del _ x h3 h2 hx).trans ?_)
  rw [hξ z (Units.mk0 _ h0) r rfl hr, Units.val_inv_eq_inv_val]
  exact congrArg _ ((congrArg _ (dif_pos h2)).trans h4)

end Place


end GlobalTheory.LowJoin

end
end
end
