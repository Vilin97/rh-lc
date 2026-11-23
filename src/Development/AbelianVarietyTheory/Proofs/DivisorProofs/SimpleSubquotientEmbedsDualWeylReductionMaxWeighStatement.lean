module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightFormOnSimpleSubquotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeylStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZeroStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupAction

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
    hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupActionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb


theorem _root_.GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  first | exact @GlobalTheory.HighWtEmb.redT_grp | exact GlobalTheory.HighWtEmb.redT_grp | (intros; apply GlobalTheory.HighWtEmb.redT_grp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReduction

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_eq_rename (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, blockRed, aeval_X, map_X, rename_X] at hp ⊢

theorem redT_tprod (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) =
      ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (x τ : MvPolynomial (Fin N × Fin N) O)) := by
  unfold redT
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
  exact blockRed_eq_rename O N ϖ τ _

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem nabK_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC P hP
  unfold nabK at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    have hl : ∀ τ, ∃ g ∈ dualWeyl O N N (res N (mu τ)),
        MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f τ :=
      fun τ => (hBC O ϖ hϖ N (res N (mu τ)) (hanti τ)).1 (f τ) (hf τ)
    choose g hg hgf using hl
    refine ⟨PiTensorProduct.tprod O (fun τ => (⟨g τ, hg τ⟩ : dualWeyl O N N (res N (mu τ)))), ?_⟩
    rw [redT_tprod]
    exact Finset.prod_congr rfl fun τ _ => by rw [hgf τ]
  | zero => exact ⟨0, map_zero _⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨z, rfl⟩ := hQ
    exact ⟨y + z, map_add _ _ _⟩
  | smul c P _ hP =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • y, ?_⟩
    rw [LinearMap.map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end GlobalTheory.HighWtEmb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReductionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb


theorem _root_.GlobalTheory.T.exists_lift_dualWeylTensorReduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  first | exact @GlobalTheory.HighWtEmb.nabK_lift | exact GlobalTheory.HighWtEmb.nabK_lift | (intros; apply GlobalTheory.HighWtEmb.nabK_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeigh

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb



theorem embeds_of_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax
  obtain ⟨z₀, hz₀, hfix⟩ := hJ
  obtain ⟨φ, hφ0, hφc, hφp⟩ := GlobalTheory.T.exists_weightForm_on_simple_subquotient O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix
  obtain ⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩ :=
    GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp
  have hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ)) := fun τ => by
    rw [GlobalTheory.HighWt.res_extW]; exact hw τ
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤
      LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ) := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]
  set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ
    (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL
  have hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y := fun y => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]
    intro y hy
    exact GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy
  have hsurj : ∀ z, ∃ q, L q = Pz z := by
    intro z
    have h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) := by
      have e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w := funext fun τ => GlobalTheory.HighWt.res_extW N w τ
      rw [e]
      haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
      letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
      exact GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lift_dualWeylTensorReduction O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1
    exact ⟨Submodule.Quotient.mk y, hy⟩
  choose q hq using hsurj
  have hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0 := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩
      · have e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g := rfl
        rw [e, hPg, hz, map_zero]
      · rw [hPp τ v _ hp, hz, map_zero]
    | algebraMap c =>
      intro z hz
      have e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c := rfl
      rw [e, hPc, hz, mul_zero]
    | add x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, add_smul, map_add (f := _), ihx z hz, ihy z hz, add_zero]
    | mul x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, mul_smul]
      exact ihx _ (ihy z hz)
  let K : Submodule (alg O N lam) Gm :=
    { carrier := {z | Pz z = 0}
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a z hz => hsm a z hz }
  have hK : K = ⊥ := by
    haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have : z₀ ∈ K := h ▸ Submodule.mem_top
      exact hPz0 this
  let ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) :=
    { toFun := q
      map_zero' := hLinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hLinj (by rw [hq, map_add (f := _), map_add (f := _), hq, hq]) }
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : Pz (a - b) = 0 := by
      rw [map_sub, ← hq a, ← hq b]
      exact sub_eq_zero.2 (congrArg L hab)
    have h2 : a - b ∈ K := h1
    rw [hK, Submodule.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · intro c z
    apply hLinj
    change L (q _) = L (c • q z)
    rw [hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  · intro g z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action, hPg, ← hq z, hzy', hLmk]
  · intro τ v a a' ha ha' z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_weightProjector O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]

end GlobalTheory.HighWtEmb

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeighStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  first | exact @GlobalTheory.HighWtEmb.embeds_of_maxWeight | exact GlobalTheory.HighWtEmb.embeds_of_maxWeight | (intros; apply GlobalTheory.HighWtEmb.embeds_of_maxWeight <;> assumption)
end
end
