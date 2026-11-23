module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffFieldStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffFieldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.branchingPairing_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowClaim.brPair_mem_coefField | exact GlobalTheory.RowClaim.brPair_mem_coefField | (intros; apply GlobalTheory.RowClaim.brPair_mem_coefField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m, AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.FormCoef.coeff_formC_mem | exact GlobalTheory.FormCoef.coeff_formC_mem | (intros; apply GlobalTheory.FormCoef.coeff_formC_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffs

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coeff

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem coeff_bVV_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) (m) :
    AddMonoidAlgebra.coeff ((bVV ℂ lam i : VV ℂ lam) : Pol ℂ ι n) m ∈ A := by
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam i
  rw [bVV_coe, hP, coeff_map]
  exact intCast_mem A _

theorem coeff_mem_of_repr_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ i, (bVV ℂ lam).repr v i ∈ A) (m) : AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A := by
  have e := congrArg (fun x : VV ℂ lam => AddMonoidAlgebra.coeff (x : Pol ℂ ι n) m) ((bVV ℂ lam).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at e
  rw [← e]
  exact sum_mem fun i _ => mul_mem (h i) (coeff_bVV_mem A lam i m)

theorem repr_mem_of_coeff_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (i : VVIdx lam) : (bVV ℂ lam).repr v i ∈ A := by
  classical
  choose P hP using fun j => bVVfun_int ℂ lam j
  let s : A →+* ℂ := A.subtype
  let b' : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) A := fun j => map (Int.castRingHom A) (P j)
  have hb' : ∀ j, map s (b' j) = ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) := fun j => by
    rw [bVV_coe, hP, map_map]
    congr 1
  obtain ⟨v', hv'⟩ : ∃ v' : MvPolynomial (ι × Fin n × Fin n) A, map s v' = (v : Pol ℂ ι n) := by
    obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := s)).2 (fun c hc => by
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact ⟨⟨_, h m⟩, rfl⟩)
    exact ⟨F', hF'⟩
  have hliC : LinearIndependent ℂ fun j => ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) :=
    (bVV ℂ lam).linearIndependent.map' (VV ℂ lam).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent A b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have e := congrArg (map s) hg

    simp only [map_sum, map_zero, smul_eq_C_mul, map_mul, map_C, hb'] at e
    have e' : ∑ k, (s (g k)) • ((bVV ℂ lam k : VV ℂ lam) : Pol ℂ ι n) = 0 := by
      simpa only [smul_eq_C_mul] using e
    have := Fintype.linearIndependent_iff.1 hliC (fun k => s (g k)) e' j
    exact Subtype.ext this
  have hspan : v' ∈ Submodule.span A (Set.range b') := by
    by_contra hn
    have hopt : LinearIndependent A (fun o : Option (VVIdx lam) => Option.casesOn' o v' b') :=
      (linearIndependent_option' (x := v') (v := b')).2 ⟨hli, hn⟩
    have hC := Formalism.L2.Col.linearIndependent_map s _ hopt
    have hC' : LinearIndependent ℂ (fun o : Option (VVIdx lam) =>
        Option.casesOn' o (map s v') fun j => map s (b' j)) := by
      convert hC using 1
      funext o
      cases o <;> rfl
    obtain ⟨-, hnot⟩ := (linearIndependent_option' (x := map s v') (v := fun j => map s (b' j))).1 hC'
    apply hnot
    rw [hv']
    have hvs := congrArg (fun x : VV ℂ lam => (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvs
    rw [← hvs]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hb' j⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have hvc : v = ∑ j, (s (c j)) • bVV ℂ lam j := by
    apply Subtype.ext

    rw [← hv', ← hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ← hb', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rw [hvc, (bVV ℂ lam).repr_sum_self]
  exact (c i).2

theorem coeff_map_mem {ι' : Type} [Fintype ι'] {n' : ℕ} (A : Subfield ℂ) (lam : ι → DomWeight n)
    (mu : ι' → DomWeight n') (f : VV ℂ lam →ₗ[ℂ] VV ℂ mu)
    (hf : ∀ a b, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ mu) f a b ∈ A) (v : VV ℂ lam)
    (hv : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (m) : AddMonoidAlgebra.coeff ((f v : VV ℂ mu) : Pol ℂ ι' n') m ∈ A := by
  classical
  refine coeff_mem_of_repr_mem A mu (f v) (fun a => ?_) m
  rw [← LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ mu) f v, Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hf a b) (repr_mem_of_coeff_mem A lam v hv b)

theorem coeff_rhoVr_mem {E : Type} [Field E] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (A : Subfield ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (γE : GL (Fin n) E) (v : VV ℂ lam) (hv : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (m) :
    AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Pol ℂ ι n) m ∈ A := by
  classical
  let R₀ : Subring (Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
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
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end Coeff

theorem chainTo_preserves {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → Prop) (hk : ∀ j v, P j v → P (j + 1) (k j v)) : ∀ N v, P 0 v → P N (GlobalTheory.FunObj.chainTo k N v)
  | 0, _, hv => hv
  | N + 1, v, hv => hk N _ (chainTo_preserves k P hk N v hv)

end GlobalTheory.RowTest.ColField

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, AddMonoidAlgebra.coeff u.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.colMap d (ch.S.ptTop c) u).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ _ β hβ τ hτ d hd c u hu
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have memK : ∀ z : ℂ, z ∈ K ↔ z ∈ Set.range D.what₂.embLL := fun z => Iff.rfl
  have hE : ∀ (σ : D.what₂.Tau) (x : D.host.E), tauE D σ x ∈ K := fun σ x =>
    ⟨labLL D σ x, GlobalTheory.Mem.R3.BrgRead.embLL_labLL_eq σ x⟩
  have hrat := (hF.isRatAt hβ hτ hd c).1
  have hu' : ∀ m, AddMonoidAlgebra.coeff (u : Pol ℂ D.what₂.Tau (ch.G.V (.top 0)).rank) m ∈ K := fun m => (memK _).2 (hu m)
  have h0 := coeff_rhoVr_mem (tauE D) (wt ch.G (.top 0)) K hE (ch.S.N.fr (.top 0))⁻¹ u hu'
  have hchain := chainTo_preserves (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v => ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ D.what₂.Tau (ch.G.V (.top j)).rank) m ∈ K) (fun j v hv => by
      by_cases h : j < D.R.m
      · simp only [dif_pos h]
        exact coeff_map_mem K _ _ _ (fun a b => (memK _).2 (hrat ⟨j, h⟩ a b)) v hv
      · simp only [dif_neg h, LinearMap.zero_apply, ZeroMemClass.coe_zero,
          AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        exact fun _ => zero_mem K) D.R.m _ h0
  intro m
  exact (memK _).1 (hchain m)

end GlobalTheory.RowTest.ColField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, AddMonoidAlgebra.coeff u.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.colMap d (ch.S.ptTop c) u).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.ColField.colMap_coeff_mem | exact GlobalTheory.RowTest.ColField.colMap_coeff_mem | (intros; apply GlobalTheory.RowTest.ColField.colMap_coeff_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningful

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest.SumRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem natCast_cpow_half (N : ℕ) (n : ℤ) : (N : ℂ) ^ ((n : ℂ) / 2) = ((Real.sqrt N : ℝ) : ℂ) ^ n := by
  have h1 : (N : ℂ) = ((N : ℝ) : ℂ) := by simp
  rw [h1, show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem sAA_mem (ch : Choice R) (h : ch.FieldOK) : ch.S.sAA ∈ D.what₂.embLL.fieldRange := by
  classical
  unfold GridChoice.sAA
  refine Subfield.prod_mem _ fun w hw => ?_
  obtain ⟨n, hn, -⟩ := aaScalar_eq_pow ch.W w (hasConductor_psiAt_AA ch.W w)
  have hq : GlobalTheory.SplitWeil.resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨y, hy⟩ := h.sqrt w (Or.inl hw)
    exact ⟨y, hy⟩
  rw [hn, hq, natCast_cpow_half]
  exact zpow_mem hs n

theorem psiC_rat (ch : Choice R) (a : Fin ch.n) (g : FinPt ch.G (.top 0)) (m) :
    AddMonoidAlgebra.coeff (psiC (ch.Psi a) g).1 m ∈ Set.range D.what₂.embLL := by
  show AddMonoidAlgebra.coeff ((GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) (ch.Psi a (finG (Xp ch.G) g))).1) m ∈ _
  simp [GlobalTheory.CoefModel.mapVV, MvPolynomial.coeff_map]

theorem vK_mem (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ) (hS : HidaSetting large₂ R F) (hi : ch.Is)
    (hsc : ch.AtScale CF b) (hK : ch.FieldOK) (hO : ∀ t a, ch.S.SumOK t (ch.Phi a)) (t : T) (x : A.fam.amb.FR t)
    (a : Fin ch.n) : vK ch t x a ∈ D.what₂.embLL.fieldRange := by
  classical
  have hR : ∀ z, z ∈ Set.range D.what₂.embLL → z ∈ D.what₂.embLL.fieldRange := fun z ⟨y, hy⟩ => ⟨y, hy⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have h := hO t a
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ∃ τ, IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) τ :=
    fun β hβ => exists_cosetExpansion_expDepth hL ch.S.toGridChoice t (ch.Phi a) β (h.ex β hβ)
  let τf : CosFam ch.G t → PureDat ch.G t →₀ ℂ := fun β =>
    if hβ : β ∈ ch.S.supp t (ch.Phi a) then (hex β hβ).choose else 0
  have hτf : ∀ β (hβ : β ∈ ch.S.supp t (ch.Phi a)), IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) (τf β) := fun β hβ => by
    simp only [τf, dif_pos hβ]; exact (hex β hβ).choose_spec
  show ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) ∈ D.what₂.embLL.fieldRange
  refine mul_mem (sAA_mem ch hK) ?_
  rw [h.vCore_eq τf fun β hβ => (hτf β hβ).2.1]
  refine sum_mem fun β hβ' => ?_
  have hβ : β ∈ ch.S.supp t (ch.Phi a) := (Set.Finite.mem_toFinset _).1 hβ'
  refine mul_mem (prod_mem fun w _ => SubfieldClass.ratCast_mem _ _) ?_
  unfold GridChoice.classSum
  haveI := h.cls β
  haveI := Fintype.ofFinite (ch.S.Classes t (ch.Phi a) β)
  rw [finsum_eq_sum_of_fintype]
  refine sum_mem fun c _ => mul_mem ?_ ?_
  · unfold GridChoice.invGam
    exact mul_mem (prod_mem fun j _ => inv_mem (natCast_mem _ _)) (prod_mem fun i _ => inv_mem (natCast_mem _ _))
  · unfold GridChoice.pairAt
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    refine sum_mem fun d hd => mul_mem ?_ ?_
    · obtain ⟨X, Y, e⟩ := (hτf β hβ).coef_eq hd
      rw [e]
      exact prod_mem fun w _ => hR _ (GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField ch large₂ F CF b hS hi hsc hK t _ h β hβ w _ _)
    · have hU := GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _ (psiC_rat ch a (ch.S.ptTop c 0))
      have hV := GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _
        (GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField ch large₂ F hS hi hK t x (ch.S.ptRow c 0))
      exact hR _ (GlobalTheory.T.branchingPairing_mem_coefficientField ch large₂ F hS hi hK t _ h (ch.S.colMap d (ch.S.ptTop c) (psiC (ch.Psi a) (ch.S.ptTop c 0)))
        (ch.S.rowMap d (ch.S.ptRow c) (ch.S.formC t (R.jX t x) (ch.S.ptRow c 0))) hU hV)

end GlobalTheory.RowTest.SumRat

namespace GlobalTheory.RowTest

theorem sumRatK_of_sumOKK : SumOKK → SumRatK := by
  rintro ⟨CF0, h⟩
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx' Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc hK t x a => ?_⟩
  obtain ⟨y, hy⟩ := SumRat.vK_mem ch large₂ F CF large₂.sc.b s hi hsc hK (hx D large₂ e hx' Γ Pl0 T A Ks R F s ch hi hsc) t x a
  exact ⟨y, hy⟩

end GlobalTheory.RowTest

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningfulStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful : GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowTest.sumRatK_of_sumOKK | exact GlobalTheory.RowTest.sumRatK_of_sumOKK | (intros; apply GlobalTheory.RowTest.sumRatK_of_sumOKK <;> assumption)
end
end
