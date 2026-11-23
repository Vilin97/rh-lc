module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColNone
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProofStatement
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumns

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwSProof

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem ramAt_fixed {p₀ : SplitPt D k} {β : Frame p₀ S n} {P : Pair k n} {φ₀ : GA D S → ℂ} (h : GlobalTheory.FinPl.RamAt β P φ₀) {g : GL n k}
    (hg : g • P = P) : rTrans (β.gl g) φ₀ = φ₀ := by
  obtain ⟨φ, ⟨heq, -, -⟩, rfl⟩ := h
  have := heq g P
  rw [hg] at this
  exact this.symm

theorem comb_foldr (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    ∃ c : GA D S →₀ ℂ, (∀ g ∈ c.support, g ∈ grpAt S fun x => ∃ i, x = (p i).v) ∧
      ∀ φ, J.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) φ = trc c φ := by
  have hsub : ∀ i, grpAt S (· = (p i).v) ≤ grpAt S fun v => ∃ i, v = (p i).v :=
    fun i => AllBij.congGrp_mono S (AllBij.idAt_mono fun v hv => ⟨i, hv⟩)
  induction J with
  | nil =>
    refine ⟨Finsupp.single 1 1, fun g hg => ?_, fun φ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]; exact Subgroup.one_mem _
    · exact (AllBij.act_single_one φ).symm
  | cons i l ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨-, -, C, -, hC, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl (η i) S (β i) (Q i)
    refine ⟨AllBij.cmul (Finsupp.mapDomain (β i).gl C) c, fun g hg => ?_, fun φ => ?_⟩
    · exact AllBij.cmul_mem (S := grpAt S fun v => ∃ i, v = (p i).v)
        (fun g h => hsub i (AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) C g h))
        (fun g h => hc g (Finsupp.mem_support_iff.2 h)) g (Finsupp.mem_support_iff.1 hg)
    · show sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) (l.foldr _ φ) = _
      rw [hl, hC, AllBij.sum_rep_eq]
      exact (AllBij.act_cmul _ _ _).symm

theorem sOp_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, -, hc, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_keeps hinj β Q q χ hχ (ε i) i ih

end Local

theorem twS : TwS' := by
  intro B X I hOk hPins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  have hinj : Function.Injective fun i => (p i).v := GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hStd
  have key : ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ → ∀ η : ι → 𝓀[k]ˣ,
      ∃ φ', RamT (I := I) (l := l) (u := u) (a := a) j φ' ∧ ∀ b y, A.rd θ j hj b φ' y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
    intro j hj φ hφ η
    obtain ⟨c, hc, hfold⟩ := comb_foldr (β j) (Q j) q χ hχ η J
    have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
    have hR : ∀ b y, IsContAut _ (trc c (A.rd θ j hj b φ y)) ∧
        ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (trc c (A.rd θ j hj b φ y)) := by
      intro b y
      rw [← hfold]
      exact foldr_keeps hinj (β j) (Q j) q χ hχ η J ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩
    obtain ⟨φ', hφ'F, hφ'⟩ := GlobalTheory.T.twistTranslationsActAtLevelPrime_proof I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj c hc φ hφ.1
      (fun b y i g hg => ramAt_fixed ((hR b y).2 i) hg)
    refine ⟨φ', ?_, fun b y => (hφ' b y).trans (hfold _).symm⟩
    have hram' := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ' hφ'F
    exact hram'.2.2 fun b y i => by rw [hφ' b y]; exact (hR b y).2 i
  classical
  refine ⟨fun j η φ => if h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ then
    (key j h.1 φ h.2 η).choose else φ, ?_⟩
  intro j hj φ hφ
  have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
  refine ⟨fun b y => ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩, fun η => ?_⟩
  have h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ := ⟨hj, hφ⟩
  simp only [dif_pos h]
  exact (key j hj φ hφ η).choose_spec

end GlobalTheory.AdForm.TwSProof

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumnsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.levelPrime_operators_act_on_ramified_columns : GlobalTheory.AdForm.TwS' := by
  first | exact @GlobalTheory.AdForm.TwSProof.twS | exact GlobalTheory.AdForm.TwSProof.twS | (intros; apply GlobalTheory.AdForm.TwSProof.twS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActRamifiedColumnsVanishing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n) (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) : sOp β P q χ ε 0 = 0 := by
  have h0 : formAt β P 0 = 0 := by
    funext P₁
    simp [formAt]
  simp [sOp, h0]

theorem foldr_sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n)
    (P : ι → Pair k n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    J.foldr (fun i f => sOp (β i) (P i) q (χ i) (η i) f) 0 = 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [List.foldr_cons, ih]; exact sOp_zero_fun _ _ _ _ _

theorem infM_one_eq {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    infM θ V hn 1 τ = 1 := by
  simp [infM, Formalism.L2.Theta.mt, Datum.compAt]

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type}

theorem TwDat.rd_eq_zero_of_vanish (A : TwDat I l Z u a Ch) (θ : InfFam (I.rec7 l Z)) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j)
    (φ : ColT I l u a j) (hφ : ∀ c, A.chOf j c = b → φ c = 0) (y : (I.chain l u a).Y j) : A.rd θ j hj b φ y = 0 := by
  funext g
  unfold TwDat.rd rdS
  split_ifs with h
  · simp [hφ _ h.choose.1.2, atFr]
    intro _
    rfl
  · rfl

theorem twS_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  intro B X I hOk hPins l Z u a Ch₀ Ch A ιc hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  obtain ⟨S, hS⟩ := GlobalTheory.T.levelPrime_operators_act_on_ramified_columns I hOk hPins l Z u a Ch₀ A hA θ hθ k ι p β Q L hStd J q χ hχ
  refine ⟨S, fun j hj φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := hS j hj φ hφ.1
  refine ⟨h1, fun η => ⟨⟨(h2 η).1, ?_⟩, (h2 η).2⟩⟩
  intro c hc
  have hrd0 : ∀ y, A.rd θ j hj (A.chOf j c) φ y = 0 := fun y =>
    TwDat.rd_eq_zero_of_vanish A θ j hj _ φ (fun c' hc' => hφ.2 c' (by rw [hc']; exact hc)) y
  have hrdS : ∀ y, A.rd θ j hj (A.chOf j c) (S j η φ) y = 0 := by
    intro y
    rw [(h2 η).2, hrd0]
    exact foldr_sOp_zero_fun _ _ _ _ _ _
  funext y'
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) 1) ⟨y'.1, y'.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_one_eq]
    first
    | exact (Matrix.one_mul _).symm
    | exact (one_mul _).symm
    | exact (one_smul _ _).symm
    | (show _ = _; simp [Matrix.one_mul])
  have key := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hA θ hθ j hj (S j η φ) (h2 η).1.1).2 (A.chOf j c) y' 1 (one_mem _)
    ⟨c, rfl⟩ 1 (one_mem _) 1 y' hTr
  rw [hrdS] at key
  simpa using key.symm

end GlobalTheory.AdForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActRamifiedColumnsVanishingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  first | exact @GlobalTheory.AdForm.twS_ramL | exact GlobalTheory.AdForm.twS_ramL | (intros; apply GlobalTheory.AdForm.twS_ramL <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadS

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam
theorem colOf_readS_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ha hat J hJ k
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  choose S hS using fun t => GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) _ _ (J t).A (J t).ι (hJ t).is (_root_.GlobalTheory.Fam.pk_z W).θ
    hat.pinX.inf a.k a.ι a.o.p a.o.β a.o.Q (fun j => (a.g.x j).L) hat.std a.o.I a.o.q a.o.χ a.o.hχ
  refine ⟨S, fun t => ⟨fun j hj η φ hφ => ((hS t j hj φ hφ).2 η).1, fun row kom dd s cV cK cP => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj ψ hψ α y
    have h := (hS t j hj ψ hψ).1 ((J t).ι j α) y
    change (if hj' : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj' ((J t).ι j α) ψ y else 0) ∈ a.o.Ram j
    have hj2 : j ≤ B.R.m := hj
    rw [dite_eq_left hj2]
    exact h
  · intro j hj ψ hψ α y
    have hj' : j ≤ B.R.m := by change j + 2 ≤ B.R.m at hj; omega
    change (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) (S t j (k.ε j) ψ) y else 0) =
      a.o.S k.ε j (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) ψ y else 0)
    rw [dite_eq_left hj', dite_eq_left hj']
    exact ((hS t j hj' ψ hψ).2 (k.ε j)).2 _ y
  · intro η ψ hψ
    have h0 : (0 : ℕ) ≤ B.R.m := Nat.zero_le _
    refine ⟨((hS t 0 h0 ψ hψ).2 η).1, fun α y => ?_⟩
    change (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) (S t 0 η ψ) y else 0) =
      a.o.S (fun _ => η) 0 (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) ψ y else 0)
    rw [dite_eq_left h0, dite_eq_left h0]
    exact ((hS t 0 h0 ψ hψ).2 η).2 _ y
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadSStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc

theorem _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  first | exact @_root_.GlobalTheory.Fam.colOf_readS_alt | exact _root_.GlobalTheory.Fam.colOf_readS_alt | (intros; apply _root_.GlobalTheory.Fam.colOf_readS_alt <;> assumption)
end
end
end
