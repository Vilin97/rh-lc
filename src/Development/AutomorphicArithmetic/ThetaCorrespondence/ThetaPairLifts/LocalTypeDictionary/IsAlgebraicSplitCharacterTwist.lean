module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Formalism.PeriodIntegrals.AlgValsFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

-- Source module: Formalism.LocalToGlobal.UnitaryNorms.CharExCol

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

open Formalism.L2.Col

variable {X : Fields} (σ₀ : X.K →+* ℂ)


end CharEx

end Formalism.L2.Host
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin

section

@[expose] public section

theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
end
end

-- Source module: Formalism.LocalToGlobal.UnitaryNorms.CharExVal

section

@[expose] public section

namespace Formalism.L2.Host

namespace CharEx

theorem algValsFin (L : Type) [Field L] [NumberField L] : AlgValsFin L := algebraic_values_finite L

end CharEx

end Formalism.L2.Host
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeLocVals

def embField (E : Type) [Field E] [NumberField E] : IntermediateField ℚ ℂ :=
  ⨆ ψ : E →+* ℂ, ψ.toRatAlgHom.fieldRange

variable {E : Type} [Field E] [NumberField E]

instance embField_fd : FiniteDimensional ℚ (embField E) := by
  haveI : ∀ ψ : E →+* ℂ, FiniteDimensional ℚ ψ.toRatAlgHom.fieldRange := fun ψ =>
    ψ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem emb_mem (ψ : E →+* ℂ) (k : E) : ψ k ∈ embField E :=
  le_iSup (fun ψ : E →+* ℂ => ψ.toRatAlgHom.fieldRange) ψ ⟨k, rfl⟩

theorem inf_mem_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) (k : Eˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ embField E := by
  rw [h k]
  refine prod_mem fun i _ => ?_
  have h0 : φ i (k : E) ≠ 0 := by simp
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ h0]
  exact zpow_mem (div_mem (emb_mem _ _) (emb_mem ((starRingEnd ℂ).comp (φ i)) (k : E))) _

theorem exists_inter_of_subfield (C : Subfield ℂ) [FiniteDimensional ℚ C] :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C : Set ℂ) ⊆ M := by
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simpa using SubfieldClass.ratCast_mem C x
  let e : C ≃ₗ[ℚ] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun q x => Subtype.ext (by simp [Rat.smul_def])
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨M, e.finiteDimensional, fun _ h => h⟩

end GlobalTheory.HeckeLocVals

namespace GlobalTheory.HeckeLocVals

variable {E : Type} [Field E] [NumberField E]

theorem zpow_fsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem algType_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) : ∃ m : (E →+* ℂ) → ℤ, ∀ k : Eˣ,
      ((χ.inf k : ℂˣ) : ℂ) * ∏ ψ : E →+* ℂ, ((‖ψ (k : E)‖ : ℝ) : ℂ) ^ (((0 : ℝ)) : ℂ) = ∏ ψ : E →+* ℂ, ψ (k : E) ^ m ψ := by
  classical
  refine ⟨fun ψ => ∑ i, ((if φ i = ψ then c i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0)), fun k => ?_⟩
  simp only [Complex.ofReal_zero, Complex.cpow_zero, Finset.prod_const_one, mul_one]
  rw [h k]
  let u : (E →+* ℂ) → ℂˣ := fun ψ => Units.mk0 (ψ (k : E)) (by simp)
  have hu : ∀ ψ (n : ℤ), ψ (k : E) ^ n = ((u ψ ^ n : ℂˣ) : ℂ) := fun ψ n => by
    rw [Units.val_zpow_eq_zpow_val]; rfl
  have hL : ∀ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ (2 * c i) =
      ((u (φ i) ^ c i * (u ((starRingEnd ℂ).comp (φ i)) ^ c i)⁻¹ : ℂˣ) : ℂ) := fun i => by
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ (by simp), div_zpow]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← hu, ← hu, div_eq_mul_inv]
    rfl
  simp_rw [hL, hu]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  symm
  rw [Finset.prod_congr rfl fun ψ _ => (zpow_fsum (u ψ) Finset.univ _).trans (Finset.prod_congr rfl fun i _ => zpow_sub (u ψ) _ _),
    Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have e1 : ∏ ψ : E →+* ℂ, u ψ ^ (if φ i = ψ then c i else 0) = u (φ i) ^ c i := by
    rw [Finset.prod_eq_single (φ i) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  have e2 : ∏ ψ : E →+* ℂ, u ψ ^ (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0) =
      u ((starRingEnd ℂ).comp (φ i)) ^ c i := by
    rw [Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  rw [e1, e2]

theorem locVals_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ v x, ((χ.loc v x : ℂˣ) : ℂ) ∈ M := by
  obtain ⟨m, hm⟩ := algType_of_even h
  obtain ⟨C, hC, hv⟩ := CharEx.algValsFin E χ 0 m hm
  obtain ⟨C', hC', hCC⟩ := exists_inter_of_subfield C
  refine ⟨C' ⊔ embField E, inferInstance, fun v x => ?_⟩
  have hle : GlobalTheory.Mem.Fld.valueField χ 0 ≤ C' ⊔ embField E := by
    rw [GlobalTheory.Mem.Fld.valueField_le_iff]
    intro w hw
    obtain ⟨y, hy⟩ := hv w hw
    exact ⟨⟨y, le_sup_left (a := C') (hCC y.2)⟩, hy⟩
  exact GlobalTheory.HeckeValField.mem_unitsIn.1
    (GlobalTheory.HeckeValField.loc_mem χ hle (fun k => le_sup_right (a := C') (inf_mem_of_even h k)) v x)

end GlobalTheory.HeckeLocVals
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitCharacterValueAlgebraic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic


open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

end GlobalTheory.SplitCharAlg
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsAlgebraicSplitCharacterTwist

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitCharAlg
open Formalism.L2.Host
open scoped TensorProduct
end GlobalTheory.SplitCharAlg
namespace GlobalTheory.SplitCharAlg
theorem splitCharacter_value_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ e : AE D, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) = e * x + (1 - e) →
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) x : Circle) : ℂ) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL _ e he x hx
  obtain ⟨w, y, rfl⟩ := exists_locIdele he x hx
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : (((G.ch.chi (D.R.m - i)) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH (D.R.m - i)).loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq _ hi1 hi2) w)
  have heta : ((L.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((L.C.eta.loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  rw [MonoidHom.mul_apply, Circle.coe_mul, MonoidHom.pow_apply, Circle.coe_pow, hchi, heta]
  exact (isAlgebraic_loc (G.ch.inf _ hi1 hi2) w y).mul ((isAlgebraic_loc L.C.isEta.inf w y).pow _)
end GlobalTheory.SplitCharAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ e : AE D, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) = e * x + (1 - e) →
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) x : Circle) : ℂ) := by
  first | exact @_root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic | exact _root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic | (intros; apply _root_.GlobalTheory.SplitCharAlg.splitCharacter_value_isAlgebraic <;> assumption)
end
end
end
