module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierTransformCosetIndicatorEqFiniteColumnTranStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.HermitianLattices.StatementJac
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateStepPsiRationalRepEqColumnsDatumStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterOneNe

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionEqColumnsTestFunction

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopPhi

theorem topPhi : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y
  have hm : R.m = s + 2 := hA.steps
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) :=
    fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrdY E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  rw [hmat]
  exact hPhi.2 E1' E1 hE1' hE1 _

end GlobalTheory.TwBridge.TopPhi
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionEqColumnsTestFunctionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  first | exact @GlobalTheory.TwBridge.TopPhi.topPhi | exact GlobalTheory.TwBridge.TopPhi.topPhi | (intros; apply GlobalTheory.TwBridge.TopPhi.topPhi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRational

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

namespace GlobalTheory.DenseBox

theorem isOpen_box_set {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : Type) [Fintype A] (c : kˣ) : IsOpen ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
  have e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) =
      ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c := by
    ext y; simp [GlobalTheory.StepData.mem_box, cball]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)

theorem support_invariance_of_dense : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  intro k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y
  have hv : DenseRange (fun y : A → E => fun a => ι (y a)) := DenseRange.piMap (fun _ => hι)
  have hM : DenseRange (fun x : Matrix A B E => x.map ι) := by
    have : DenseRange (fun x : A → B → E => fun a b => ι (x a b)) :=
      DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
    exact this
  have hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y} := hf.isOpen_fiber _
  refine ⟨fun hne => ?_, fun z hz => ?_⟩
  ·
    let U : Set (Matrix A B k × (A → k)) :=
      {p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}
    have hU : IsOpen U := hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))
    have hxy : (x, y) ∈ U := ⟨rfl, by simp⟩
    obtain ⟨⟨x0, y0⟩, hp⟩ := (hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩
    obtain ⟨h1, h2⟩ := hp
    have hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0 := by
      simp only [Set.mem_setOf_eq, Prod.map] at h1; rw [h1]; exact hne
    have hy0 := hsupp x0 y0 hne'
    have h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹ := h2
    have := Submodule.sub_mem _ hy0 h2'
    simpa using this
  ·
    have hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)} := hf.isOpen_fiber _
    let V : Set (Matrix A B k × (A → k) × (A → k)) :=
      {q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩
        {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}
    have hV : IsOpen V := by
      refine (IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))
      · exact hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      · exact hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add
          (continuous_snd.comp continuous_snd)))
    have hxyz : (x, y, z) ∈ V := ⟨⟨rfl, rfl⟩, hz⟩
    obtain ⟨⟨x0, y0, z0⟩, hp⟩ := (hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3
    have e := hinv x0 y0 z0 h3
    have e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a)) := by
      funext a; simp
    rw [e'] at e
    rw [← h2, e, h1]

end GlobalTheory.DenseBox
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRationalStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  first | exact @GlobalTheory.DenseBox.support_invariance_of_dense | exact GlobalTheory.DenseBox.support_invariance_of_dense | (intros; apply GlobalTheory.DenseBox.support_invariance_of_dense <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumns

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.TwLast

theorem toLoc_of_mat {E k A B : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : E →+* k) {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : Matrix A B E) :
    x.map ι = toLoc ι e e' (Matrix.toLin' (Matrix.of fun i j => x (e.symm i) (e'.symm j))) := by
  ext i j
  simp [toLoc, Matrix.toLin'_apply, Matrix.mulVec_single, Function.swap]

theorem psi_isLocallyConstant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (R : Ranks) (W : TwData k) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k) :
    IsLocallyConstant (fun p : Matrix (XIx (Fin R.k) (Fin R.t) (s + 1)) (XIx (Fin R.k) (Fin R.t) s) k × (XIx (Fin R.k) (Fin R.t) (s + 1) → k) =>
      (W.T s R).Psi g p.1 p.2) := by
  have hΦ : (W.T s R).Phi s 0 rfl ∈ SB _ := (Chain.ofTwist_regular _ _ _ _ _).1 s 0 rfl
  unfold Chain.Psi om
  refine (IsLocallyConstant.const _).mul (hΦ.1.comp_continuous ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_pi fun r => continuous_pi fun c => ?_
  rcases r with r | r <;> rcases c with c | c
  · exact (continuous_apply c).comp ((continuous_apply r).comp continuous_fst)
  · exact (continuous_apply r).comp continuous_snd
  · exact r.elim0
  · exact r.elim0

theorem lastAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL
  have hPhi := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hnm : P.1 ∉ Pr.vGs := hA.nmem
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  refine ⟨fun al g hg => ⟨fun x₀ y => ?_, fun e' e he' he x₀ y' =>
    GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg e' e he' he x₀ y'⟩, ?_⟩
  · have hrat := GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg
      (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.MatchCompare.isOrd_ordX R s) (GlobalTheory.MatchCompare.isOrd_ordX R (s + 1))
    refine GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational k X.E ι hA.compl.dense _ _ ((W.T s R).Psi g) (psi_isLocallyConstant s R W g) (W.ϖ ^ cst.M) ?_ ?_ x₀ y
    · intro x y hne
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x] at hne
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))] at hne
      have hs := hL.psiSupp al P _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      rw [if_neg hnm] at hs
      rw [mem_box]
      intro a
      have h1 := hs ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)
      simp only [Equiv.symm_apply_apply] at h1
      have h' := (hint _).2 h1
      rw [map_mul, map_pow, ← hϖ] at h'
      have hϖ0 : ((W.ϖ : k) ^ cst.M) ≠ 0 := pow_ne_zero _ W.ϖ.ne_zero
      calc valuation k (ι (y a)) = valuation k (((W.ϖ : k) ^ cst.M)⁻¹ * ((W.ϖ : k) ^ cst.M * ι (y a))) := by
            rw [inv_mul_cancel_left₀ hϖ0]
        _ = valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * valuation k ((W.ϖ : k) ^ cst.M * ι (y a)) := map_mul _ _ _
        _ ≤ valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * 1 := by gcongr; exact (Valuation.mem_integer_iff _ _).1 h'
        _ = valuation k (((W.ϖ ^ cst.M)⁻¹ : kˣ) : k) := by simp
    · intro x y z hz
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x]
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      have hyz : (fun a => ι (y a + z a)) = fun a => ι (((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) +
          (fun i => z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hyz, hrat, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)), hL.psiInv al P _ _ _ ?_]
      rw [if_neg hnm]
      intro i
      apply (hint _).1
      rw [mem_box] at hz
      have h1 := hz ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)
      rw [map_mul, map_inv₀, map_pow, ← hϖ, Valuation.mem_integer_iff, map_mul, map_inv₀]
      have hv0 : valuation k ((W.ϖ : k) ^ cst.M) ≠ 0 := by simp
      calc (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k (ι (z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)))
          ≤ (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k ((W.ϖ : k) ^ cst.M) :=
            by gcongr; simpa using h1
        _ = 1 := inv_mul_cancel₀ hv0
  · intro e' e he' he y y' hy'
    simp only [Chain.xiTop]
    rw [GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hA hPhi e' e he' he y,
      GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA (hL.depthQ P hnm) e' e he' he y y' hy', map_mul]

end GlobalTheory.TwLast
end
end
end
