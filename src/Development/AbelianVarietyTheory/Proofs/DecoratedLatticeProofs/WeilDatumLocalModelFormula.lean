module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSplitLocalModelBySupportedPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubstStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilVacuumLocalModelIntegralMatrixPairStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLocalSupportedScalarComponent

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocScalar

theorem place_ι_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have hx : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]
  have := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at this
  rw [this, ← mul_assoc, hx]

theorem place_ι_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have := p.ι_π 1
  rwa [map_one, mul_one] at this

theorem place_π_e {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  rw [← place_ι_one, p.π_ι]

theorem exists_isLoc_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  intro D k _ _ _ _ p V Z _ _ F c zk hzk
  have he := p.split
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv V)
    (GlobalTheory.SplitOnto.gram_conj V) he.1 he.2.1 (p.ι (c : k) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (p.ι ((c⁻¹ : kˣ) : k) • 1) (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul (p.ι _), ← place_ι_mul, Units.inv_mul, place_ι_one, smul_smul, he.1])
  let z : GA D V := ⟨g, h1⟩
  refine ⟨z, fun i j => congrFun (congrFun h2 i) j, ?_⟩
  rw [hzk, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, F.βγ]
  ext i j
  have := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  change p.π (g.1 i j) = _
  rw [← one_mul (p.π (g.1 i j)), ← place_π_e p, ← map_mul, this, map_mul, place_π_e, one_mul]
  by_cases hij : i = j
  · subst hij; simp [p.π_ι]
  · simp [hij]

end GlobalTheory.LocScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLocalSupportedScalarComponentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.exists_splitLocal_supported_scalar_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  first | exact @GlobalTheory.LocScalar.exists_isLoc_scalar | exact GlobalTheory.LocScalar.exists_isLoc_scalar | (intros; apply GlobalTheory.LocScalar.exists_isLoc_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelInv

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv_of_unit (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem nabs_pos_of_unit (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact NNReal.coe_pos.mpr distribHaarChar_pos

theorem linearFormula_inv_cancel {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (μS μT : kˣ →* ℂˣ)
    (gk : GL Y' k) (hk : GL Y k) (Φ : Matrix Y Y' k → ℂ) :
    (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk
      ((((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk⁻¹) : ℂˣ) : ℂ) • om μS⁻¹ gk⁻¹ hk⁻¹ Φ) = Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  have hx : ((↑(hk⁻¹⁻¹) : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) *
      (↑(gk⁻¹) : Matrix Y' Y' k)) = x := by
    simp only [inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hx]
  simp only [map_inv, nabs_inv_of_unit, Units.val_inv_eq_inv_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  have p1 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det gk)
  have p2 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det hk)
  rw [Real.inv_rpow p1.le, Real.inv_rpow p2.le]
  push_cast
  simp only [neg_div]
  have q1 : ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p1 _).ne'
  have q2 : ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-((Fintype.card Y' : ℝ) / 2)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p2 _).ne'
  have u1 := (μS (Matrix.GeneralLinearGroup.det gk)).ne_zero
  have u2 := (μS (Matrix.GeneralLinearGroup.det hk)).ne_zero
  have u3 := (μT (Matrix.GeneralLinearGroup.det gk)).ne_zero
  field_simp

theorem lawLoc_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k),
    LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g⁻¹ gk⁻¹ h⁻¹ hk⁻¹ := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g gk h hk hL Φ Φ' hΦ'
  have e : ω (g, h) (Tm Φ') = Tm Φ := hL Φ' Φ (by rw [hΦ', linearFormula_inv_cancel])
  rw [← e, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel]
  change ω 1 (Tm Φ') = Tm Φ'
  rw [map_one, Module.End.one_apply]

end GlobalTheory.LocOm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelInvStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.linearLaw_localModel_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g⁻¹ gk⁻¹ h⁻¹ hk⁻¹ := by
  first | exact @GlobalTheory.LocOm.lawLoc_inv | exact GlobalTheory.LocOm.lawLoc_inv | (intros; apply GlobalTheory.LocOm.lawLoc_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelMulClosed

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm.LawMul

theorem om_smul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (c : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring

theorem lawLoc_mul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g g' : GA D S) (gk gk' : GL Y' k) (h h' : GA D T) (hk hk' : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g' gk' h' hk' → LawLoc ω μS μT Tm (g * g') (gk * gk') (h * h') (hk * hk') := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g g' gk gk' h h' hk hk' H H' Φ Φ' hΦ
  let Φ₁ : SB (Matrix Y Y' k) :=
    ⟨(((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk') : ℂˣ) : ℂ) • om μS⁻¹ gk' hk' Φ.1,
      Submodule.smul_mem _ _ (GlobalTheory.SplitWeil.Model.om_mem_SB _ _ _ Φ.2)⟩
  have h1 : ω (g', h') (Tm Φ) = Tm Φ₁ := H' Φ Φ₁ rfl
  have h2 : ω (g, h) (Tm Φ₁) = Tm Φ' := by
    refine H Φ₁ Φ' ?_
    rw [hΦ, GlobalTheory.SplitWeil.Model.om_mul, map_mul, map_mul, Units.val_mul, mul_smul]
    simp only [Φ₁, om_smul]
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.LocOm.LawMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelMulClosedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.linearLaw_localModel_mul_closed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g g' : GA D S) (gk gk' : GL Y' k) (h h' : GA D T) (hk hk' : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g' gk' h' hk' → LawLoc ω μS μT Tm (g * g') (gk * gk') (h * h') (hk * hk') := by
  first | exact @GlobalTheory.LocOm.LawMul.lawLoc_mul | exact GlobalTheory.LocOm.LawMul.lawLoc_mul | (intros; apply GlobalTheory.LocOm.LawMul.lawLoc_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInvStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.splitLocalComponents_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  first | exact @GlobalTheory.LocOm.isLoc_one_mul_inv | exact GlobalTheory.LocOm.isLoc_one_mul_inv | (intros; apply GlobalTheory.LocOm.isLoc_one_mul_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm

theorem omLoc : ∀ (D : D7), OmLoc D := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT hμS hμT Y Y' _ _ _ _ FS FT Tm hTm g gk h hk hg hh Φ Φ' hΦ'
  have U := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hW.std).1
  have enl : ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk →
      LawLoc ω μS μT Tm g gk h hk := by
    intro g gk h hk hg hh he
    obtain ⟨T₂, hT₂, hT₂e⟩ := GlobalTheory.T.conj_splitLocalModel_by_supported_pair D k p ψ S T χS χT ω hW μS μT Y Y' FS FT Tm hTm g gk h hk hg hh
    obtain ⟨Φ₀, Φ₀', h0, h0', hv⟩ := GlobalTheory.T.weil_vacuum_local_model_integral_matrix_pair D k p ψ S T χS χT ω hW μS μT hμS hμT Y Y' FS FT Tm hTm g gk h hk hg hh he
    have inv1 : ∀ F, ω (g⁻¹, h⁻¹) (ω (g, h) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have inv2 : ∀ F, ω (g, h) (ω (g⁻¹, h⁻¹) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hT : T₂ = Tm := U T₂ Tm hT₂ hTm Φ₀ h0 (by rw [hT₂e Φ₀ Φ₀' h0', ← hv, inv1])
    intro Φ Φ' hΦ'
    have := hT₂e Φ Φ' hΦ'
    rw [hT] at this
    rw [this, inv2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_preservesIntegralMatricesSubst k Y Y' gk hk
  obtain ⟨zk, hzk⟩ : ∃ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) :=
    ⟨Units.map (Matrix.scalar Y : k →+* Matrix Y Y k).toMonoidHom c, by
      simp [Matrix.smul_one_eq_diagonal]⟩
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_splitLocal_supported_scalar_component D k p T Y FT c zk hzk
  have iS := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p S Y' FS
  have iT := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p T Y FT
  have l1 := enl g gk (h * z⁻¹) (hk * zk⁻¹) hg (iT.2.1 _ _ _ _ hh (iT.2.2 _ _ hz)) (hc zk hzk).1
  have l2 := enl 1 1 z⁻¹ zk⁻¹ iS.1 (iT.2.2 _ _ hz) (hc zk hzk).2
  have l3 := GlobalTheory.T.linearLaw_localModel_mul_closed D k S T ω μS μT Y Y' Tm _ _ _ _ _ _ _ _ l1 (GlobalTheory.T.linearLaw_localModel_inv D k S T ω μS μT Y Y' Tm _ _ _ _ l2)
  simp only [inv_one, mul_one, inv_inv, inv_mul_cancel_right] at l3
  exact l3 Φ Φ' hΦ'

end GlobalTheory.LocOm

end
end
end
