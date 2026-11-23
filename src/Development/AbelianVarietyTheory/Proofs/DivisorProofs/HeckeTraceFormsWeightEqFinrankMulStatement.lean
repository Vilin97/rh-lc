module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjective
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftOfFiniteTensorProductComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRangeStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjectiveStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.automorphic_map_phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  exact @GlobalTheory.BCT.TrKer.Phi_injective
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionE

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x

    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU (E := E) (n := n)) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU (E := E) (n := n)) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU (E := E) (n := n)) :
    rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionEStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  first | exact @GlobalTheory.BCT.TrKer.hop_phiFun_comm | exact GlobalTheory.BCT.TrKer.hop_phiFun_comm | (intros; apply GlobalTheory.BCT.TrKer.hop_phiFun_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctions

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dite_eq_right h2, dite_eq_right hy]

theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dite_eq_right h2, dite_eq_right hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU (E := E) (n := n)) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU (E := E) (n := n), (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K')) q =
        ((k * q.out : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctionsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | exact GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | (intros; apply GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMul

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem trace_map_id {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (A : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ (M ⊗[ℂ] W) (TensorProduct.map A LinearMap.id) =
      LinearMap.trace ℂ M A * Module.finrank ℂ W := by
  rw [GlobalTheory.trace_tensorProduct_map_complex, LinearMap.trace_id]

theorem trOn_forms_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  intro E _ _ _ hE n hn S hS lam K' hK f hf
  have hinj := GlobalTheory.T.automorphic_map_phi_injective E hE n hn S hS lam K' hK
  have hrange : LinearMap.range (Phi S lam K') = forms S lam K' :=
    le_antisymm (GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel E hE n hn S hS lam K' hK) (GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range E hE n hn S hS lam K' hK)
  have hM := GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions E n S lam K' hK f hf
  let A := (hopM S lam K' f).restrict hM
  have hcomm : ∀ x, hop S K' f (Phi S lam K' x) = Phi S lam K' (TensorProduct.map A LinearMap.id x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul F w =>
      rw [TensorProduct.map_tmul, Phi_tmul, Phi_tmul, GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have hF : ∀ v ∈ forms S lam K', hop S K' f v ∈ forms S lam K' := by
    intro v hv
    rw [← hrange] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    exact ⟨_, (hcomm x).symm⟩
  obtain ⟨e, hev⟩ : ∃ e : (vecM S lam K' ⊗[ℂ] Wsp lam) ≃ₗ[ℂ] forms S lam K',
      ∀ y, ((e y : forms S lam K') : UA E n → ℂ) = Phi S lam K' y :=
    ⟨(LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun y => rfl⟩
  have he : (hop S K' f).restrict hF = e.conj (TensorProduct.map A LinearMap.id) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv : (v : UA E n → ℂ) = Phi S lam K' (e.symm v) :=
      (congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (e.apply_symm_apply v)).symm.trans (hev _)
    calc (((hop S K' f).restrict hF v : forms S lam K') : UA E n → ℂ) = hop S K' f v :=
          LinearMap.restrict_coe_apply _ _ v
      _ = hop S K' f (Phi S lam K' (e.symm v)) := congrArg _ hv
      _ = Phi S lam K' (TensorProduct.map A LinearMap.id (e.symm v)) := hcomm _
      _ = ((e (TensorProduct.map A LinearMap.id (e.symm v)) : forms S lam K') : UA E n → ℂ) := (hev _).symm
      _ = ((e.conj (TensorProduct.map A LinearMap.id) v : forms S lam K') : UA E n → ℂ) :=
          congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (LinearEquiv.conj_apply_apply _ _ _).symm
  have h1 : trOn (forms S lam K') (hop S K' f) = LinearMap.trace ℂ _ ((hop S K' f).restrict hF) := dif_pos hF
  have h2 : trOn (vecM S lam K') (hopM S lam K' f) = LinearMap.trace ℂ _ A := dif_pos hM
  rw [h1, h2]
  exact (congrArg (LinearMap.trace ℂ _) he).trans
    ((LinearMap.trace_conj' _ e).trans ((trace_map_id A).trans (mul_comm _ _)))

end GlobalTheory.BCT.TrKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMulStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  first | exact @GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | exact GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | (intros; apply GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul <;> assumption)
end
end
