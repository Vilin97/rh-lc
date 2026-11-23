module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficientsStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModels

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.CoefDim


open Classical in
theorem finrank_piTensorProduct {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  let b := Basis.piTensorProduct (fun i => Module.finBasis ℂ (E i))
  rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
  simp [Fintype.card_fin]

theorem finrank_coef_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB
  have hp := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hb := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.H τ) := fun τ => (m τ).1
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => inferInstance
  have hsm : ∀ τ, Module.finrank ℂ (R.MX.sm τ) = Module.finrank ℂ (R.MX.H τ) := fun τ => by
    rw [(m τ).2.1, finrank_top]
  have e : R.cX.W ≃ₗ[ℂ] Module.Dual ℂ (SmT R.MX) := LinearEquiv.ofBijective R.prX hb
  have hT : Module.finrank ℂ (SmT R.MX) = ∏ τ, Module.finrank ℂ (R.MX.H τ) :=
    (finrank_piTensorProduct (fun τ => R.MX.sm τ)).trans (Finset.prod_congr rfl fun τ _ => hsm τ)
  haveI : FiniteDimensional ℂ (SmT R.MX) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun τ => Module.finBasis ℂ (R.MX.sm τ)))
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hT]

end GlobalTheory.CoefDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  first | exact @GlobalTheory.CoefDim.finrank_coef_eq_prod | exact GlobalTheory.CoefDim.finrank_coef_eq_prod | (intros; apply GlobalTheory.CoefDim.finrank_coef_eq_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProd

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem

theorem rieszProd_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hI v v' a a' ha ha'
  classical
  have hp : GlobalTheory.DefLift.AllPlus R.MX := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hbij := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => by haveI := (m τ).1; infer_instance
  let b := fun τ => stdOrthonormalBasis ℂ (R.MX.sm τ)
  let c : R.MX.Vec → (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))) → ℂ := fun u f => ∏ τ, ⟪(b τ (f τ)), u τ⟫_ℂ
  have hexp : ∀ u : R.MX.Vec, PiTensorProduct.tprod ℂ u =
      ∑ f, c u f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := by
    intro u
    conv_lhs => rw [show u = fun τ => ∑ i, ⟪b τ i, u τ⟫_ℂ • b τ i from funext fun τ => ((b τ).sum_repr' (u τ)).symm]

    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact MultilinearMap.map_smul_univ _ (fun τ => ⟪b τ (f τ), u τ⟫_ℂ) (fun τ => b τ (f τ))
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have hB' : ∀ f, B f = PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := fun f => by
    simp [B, Basis.piTensorProduct_apply]

  have hw : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∃ w, ∀ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX w (PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = if f = g then 1 else 0 := by
    intro g
    obtain ⟨w, hw⟩ := hbij.2 (B.coord g)
    refine ⟨w, fun f => ?_⟩
    rw [hw, ← hB', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hcoef : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX a (PiTensorProduct.tprod ℂ (fun τ => b τ (g τ))) = starRingEnd ℂ (c v g) := by
    intro g
    obtain ⟨w, hw⟩ := hw g
    have h1 := hI (fun τ => Fin (Module.finrank ℂ (R.MX.sm τ))) b w a
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [hw f, if_neg hf]; simp) (by simp), hw g, if_pos rfl,
      map_one, one_mul] at h1

    rw [← h1, ← inner_conj_symm, ← ha w, hexp v, map_sum]
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [map_smul, hw f, if_neg hf]; simp) (by simp)]
    rw [map_smul, hw g, if_pos rfl, smul_eq_mul, mul_one]
  have h2 := ha' a

  rw [← h2, hexp v', map_sum]
  have hr : ∀ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ i, ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ := fun τ =>
    (Submodule.coe_inner (R.MX.sm τ) (v τ) (v' τ)).symm.trans ((b τ).sum_inner_mul_inner (v τ) (v' τ)).symm
  have hprod : ∏ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∏ τ, (⟪v τ, b τ (f τ)⟫_ℂ * ⟪b τ (f τ), v' τ⟫_ℂ) := by
    exact (Finset.prod_congr rfl fun τ _ => hr τ).trans
      (Fintype.prod_sum (fun τ (i : Fin (Module.finrank ℂ (R.MX.sm τ))) => ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ))
  refine Eq.trans ?_ hprod.symm
  refine Finset.sum_congr rfl fun f _ => ?_
  have e1 : R.prX a (c v' f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = c v' f * starRingEnd ℂ (c v f) :=
    ((R.prX a).map_smul _ _).trans ((congrArg (c v' f • ·) (hcoef f)).trans (smul_eq_mul _ _))
  refine e1.trans ?_
  have e2 : starRingEnd ℂ (c v f) = ∏ τ, ⟪v τ, b τ (f τ)⟫_ℂ :=
    (map_prod (starRingEnd ℂ) _ _).trans (Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _)
  refine (congrArg (c v' f * ·) e2).trans ?_
  refine (Finset.prod_mul_distrib).symm.trans ?_
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.Mem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProdStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.Mem.rieszProd_inner | exact GlobalTheory.Mem.rieszProd_inner | (intros; apply GlobalTheory.Mem.rieszProd_inner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInner

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.TopSchur

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem exists_vec_prod_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {W : Type}
    [AddCommGroup W] [Module ℂ W] (pr : W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (hpr : pr ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical
  have hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0 := by
    intro τ
    by_contra hz
    push_neg at hz
    apply hpr
    have hs : ∀ s : SmT M, s = 0 := by
      intro s
      induction s using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine LinearMap.ext fun w => LinearMap.ext fun s => ?_
    rw [hs s]
    simp
  choose v hv using hτ
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩
  intro h0
  exact hv τ (Subtype.ext h0)

theorem alg_step {d I p q x : ℂ} (hd : d ≠ 0) (hI : d * I = q * x) (hq : q = p) : I = x / d * p := by
  subst hq
  field_simp
  linear_combination hI

theorem dualNumber_unit_mul_decomposition {P c d x : ℂ} (hP : P = d) (hc : c = x / d) (hd : d ≠ 0) : P * c = x := by
  subst hP hc
  field_simp



theorem topSchur : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'
  classical
  have hC := GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models D G Pl0 T A Ks R F hB
  haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1
  have hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0 := by
    have := Module.finrank_pos (R := ℂ) (M := R.cX.W)
    exact_mod_cast this.ne'
  have hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ) := by
    rw [hC]; push_cast; rfl
  have key : ∀ v v' : R.MX.Vec,
      IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧
      ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v') ∂(R.νX t) =
      ⟪h, h'⟫_ℂ / (Module.finrank ℂ R.cX.W : ℂ) * ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
    intro v v'
    have hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    have hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    obtain ⟨a, ha⟩ := hr
    obtain ⟨a', ha'⟩ := hr'
    have hA := GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t h h' a a'
    obtain ⟨hint, hval⟩ := hA
    have hab := GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod D G Pl0 T A Ks R F hB hP v v' a a' ha ha'
    simp only [ha, ha']
    refine ⟨hint, ?_⟩
    exact alg_step hd0 hval hab
  have hv := exists_vec_prod_ne R.MX R.prX hB.models.prX.1
  obtain ⟨v0, hv0⟩ := hv
  unfold ipMT Mult.ipM
  split_ifs with hex
  · have e1 := (hex.choose_spec v0 v0).2
    have hch : hex.choose * _ = _ * _ := e1.symm.trans (key v0 v0).2
    have hch' := mul_right_cancel₀ hv0 hch
    exact dualNumber_unit_mul_decomposition hcast hch' hd0
  · exfalso
    exact hex ⟨_, fun v v' => key v v'⟩

end GlobalTheory.Mem.TopSchur
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInnerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.TopSchur.topSchur | exact GlobalTheory.Mem.TopSchur.topSchur | (intros; apply GlobalTheory.Mem.TopSchur.topSchur <;> assumption)
end
end
