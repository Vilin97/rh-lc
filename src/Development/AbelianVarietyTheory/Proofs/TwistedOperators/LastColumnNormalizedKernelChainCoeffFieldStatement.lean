module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange

section

@[expose] public section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRho

theorem coeff_rhoVr_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  classical
  intro ι _ n E _ emb L _ κ hA0 lam γE v hv0 m
  set A : Subfield ℂ := κ.fieldRange with hAdef
  have hA : ∀ τ x, emb τ x ∈ A := fun τ x => RingHom.mem_fieldRange.2 (hA0 τ x)
  have hv : ∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A := fun m => RingHom.mem_fieldRange.2 (hv0 m)
  rw [← RingHom.coe_fieldRange]
  show AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A
  let R₀ : Subring (Formalism.L2.DIV.Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Formalism.L2.DIV.Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (AddMonoidAlgebra.coeff F' m).2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end GlobalTheory.RowRho
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRangeStatement

section

@[expose] public section

open Formalism.L2.DIV MvPolynomial

theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange

section

@[expose] public section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowFun

theorem coeff_mem_of_mul_eq {s : Type} (K' : Subfield ℂ) (f P Q : MvPolynomial s ℂ) (hP : P ≠ 0)
    (hPK : ∀ m, AddMonoidAlgebra.coeff P m ∈ K') (hQ : ∀ m, AddMonoidAlgebra.coeff Q m ∈ K') (h : f * P = Q) :
    ∀ m, AddMonoidAlgebra.coeff f m ∈ K' := by
  classical
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.RowRat.exists_proj K'
  let g : MvPolynomial s ℂ := ∑ m ∈ f.support, monomial m (φ (AddMonoidAlgebra.coeff f m))
  have hg : ∀ m, AddMonoidAlgebra.coeff g m = φ (AddMonoidAlgebra.coeff f m) := by
    intro m
    simp only [g, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.mp hm, map_zero]
  have key : g * P = f * P := by
    ext m
    have hfix : AddMonoidAlgebra.coeff (f * P) m = φ (AddMonoidAlgebra.coeff (f * P) m) := by
      rw [h]; exact (hφ1 ⟨_, hQ m⟩).symm

    rw [hfix, coeff_mul, coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hg]
    have hs := φ.map_smul (⟨AddMonoidAlgebra.coeff P x.2, hPK _⟩ : K') (AddMonoidAlgebra.coeff f x.1)
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul] at hs
    rw [mul_comm, ← hs, mul_comm]
  have hgf : g = f := mul_right_cancel₀ hP key
  intro m
  rw [← hgf, hg]
  exact hφ2 _

theorem coeff_funOf_mem_range {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type}
    [Field L] (κ : L →+* ℂ) (hR : GlobalTheory.FunObj.ReadOK σ) (F : VV ℂ σ)
    (hF : ∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) :
    ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  classical
  have hf := hR.1 F
  unfold GlobalTheory.FunObj.IsFunForm at hf
  let G : MvPolynomial (ι × Fin n × Fin n) L :=
    ∑ m ∈ (F.1 : MvPolynomial (ι × Fin n × Fin n) ℂ).support,
      monomial m (Function.invFun κ (AddMonoidAlgebra.coeff F.1 m))
  have hG : MvPolynomial.map κ G = F.1 := by
    ext m
    rw [coeff_map]
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · exact Function.invFun_eq (hF m)
    · simp [notMem_support_iff.mp hm]
  have hmem : ∀ (p : MvPolynomial (ι × Fin n × Fin n) L) m,
      AddMonoidAlgebra.coeff (MvPolynomial.map κ p) m ∈ κ.fieldRange := fun p m => by
    rw [coeff_map]; exact RingHom.mem_fieldRange_self κ _
  have hmem_eq₁ : MvPolynomial.map κ (∏ τ, Formalism.L2.Ker.frDet L n τ ^ ∑ a, (σ τ).natW a)
      = ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ ∑ a, (σ τ).natW a := by
    simp only [map_prod, map_pow, GlobalTheory.BrRat.map_frDet]
  have hmem_eq₂ : MvPolynomial.map κ (GlobalTheory.FunObj.dualSubst L ι n G *
      ∏ τ, Formalism.L2.Ker.frDet L n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat)
      = GlobalTheory.FunObj.dualSubst ℂ ι n F.1 *
      ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    simp only [map_mul, map_prod, map_pow, GlobalTheory.BrRat.map_frDet, GlobalTheory.BrRat.map_dualSubst, hG]
  intro m
  have := coeff_mem_of_mul_eq κ.fieldRange _ _ _
    (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.funFrDet_ne_zero τ))
    (fun m => by
      rw [← hmem_eq₁]; exact hmem _ m)
    (fun m => by
      rw [← hmem_eq₂]; exact hmem _ m) hf m
  exact RingHom.mem_fieldRange.mp this

end GlobalTheory.RowFun
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRangeStatement

section

@[expose] public section

open Formalism.L2.DIV MvPolynomial

theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowFun.coeff_funOf_mem_range | exact GlobalTheory.RowFun.coeff_funOf_mem_range | (intros; apply GlobalTheory.RowFun.coeff_funOf_mem_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem embLL_labLL {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem rowMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ hSum β hβ τ hτ d hd c v hv
  have h0 := GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range _ D.what₂.embLL hSum.read.1 v hv
  have h1 := GlobalTheory.T.coeff_coefficientSpaceAction_mem_range (tauE D) D.what₂.embLL (fun τ x => ⟨labLL D τ x, embLL_labLL τ x⟩) _
    (ch.S.N.fr (.grid 0 D.R.m))⁻¹ _ h0
  have gen : ∀ (k : ∀ i, VV ℂ (wt ch.G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt ch.G (.grid (i + 1) D.R.m))),
      (∀ i (w : VV ℂ (wt ch.G (.grid i D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (k i w).1 m ∈ Set.range D.what₂.embLL) →
      ∀ j (w : VV ℂ (wt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (chainTo (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) k j w).1 m ∈ Set.range D.what₂.embLL := by
    intro k hk j
    induction j with
    | zero => intro w hw; exact hw
    | succ j ih => intro w hw; exact hk j _ (ih w hw)
  simp only [GlobalTheory.FunObj.GridChoice.rowMap, LinearMap.comp_apply]
  refine gen _ (fun i w hw m => ?_) D.R.m _ h1
  split_ifs with h
  · refine coeff_map_mem _ _ ?_ w hw m
    intro a b
    have := (hF.isRatAt hβ hτ hd c).2 ⟨i, h⟩ a b
    simpa [GlobalTheory.FunObj.Normal.IsRatAt, GlobalTheory.FunObj.Normal.IsRatIn, GlobalTheory.FunObj.Normal.kkIn, LinearMap.toMatrix_apply] using this
  · exact ⟨0, by simp⟩

end GlobalTheory.RowRat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowRat.rowMap_coeff_mem | exact GlobalTheory.RowRat.rowMap_coeff_mem | (intros; apply GlobalTheory.RowRat.rowMap_coeff_mem <;> assumption)
end
end
