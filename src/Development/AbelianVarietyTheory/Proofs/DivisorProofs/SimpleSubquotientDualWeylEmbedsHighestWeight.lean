module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointRowWeightDualWeylModuleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomain
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
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotential
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeighStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), GlobalTheory.HighWt.CoefIn O N lam := by
  first | exact @GlobalTheory.HighWt.coefIn_of_domain | exact GlobalTheory.HighWt.coefIn_of_domain | (intros; apply GlobalTheory.HighWt.coefIn_of_domain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChange

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChangeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.highest_weight_base_change : GlobalTheory.HighWt.BaseChange := by
  first | exact @GlobalTheory.HighWt.baseChange_holds | exact GlobalTheory.HighWt.baseChange_holds | (intros; apply GlobalTheory.HighWt.baseChange_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotentialStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.jointRowWeight_antitone_of_maxPotential : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → ∀ τ, Antitone (w τ) := by
  first | exact @GlobalTheory.HighWt.antitone_of_pot_max | exact GlobalTheory.HighWt.antitone_of_pot_max | (intros; apply GlobalTheory.HighWt.antitone_of_pot_max <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightBoundsDualWeylModule

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem dualWeyl_rowDeg_dominance (O : Type) [CommRing O] [IsDomain O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [standardMonomialSpanDomain O N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bideterminantDominance O N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem rename_rowPerm_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ dualWeyl O N N ν := by
  classical
  have h : (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) : MvPolynomial (Fin N × Fin N) O →ₐ[O] _) =
      rowAct O (Matrix.of fun a b : Fin N => if σ a = b then (1 : O) else 0) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct]
  rw [h]
  exact dualWeylRowStable O N N ν _ f hf

theorem weight_rowW_eq_rowDeg {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

open MvPolynomial Formalism.GradedWeylDivisibility

theorem sum_fin_lt_one {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) : ∑ b : Fin N with b.val < 1, g b = g ⟨0, h⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨0, h⟩ : Fin N) (by simp)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem sum_fin_split_last {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) :
    ∑ b : Fin N, g b = ∑ b : Fin N with b.val < N - 1, g b + g ⟨N - 1, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin N => b.val < N - 1)]
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨N - 1, by omega⟩ : Fin N) (by simp; omega)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem jointWt_bounds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧
      ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  intro O _ _ _ _ N ι _ _ lam _ Gm _ _ w hw τ
  classical
  obtain ⟨z, hz0, hz⟩ := hw
  obtain ⟨a0, ha0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ (w τ)
  have hmem : a0 ∈ alg O N lam := Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha0⟩)
  have hex : ∃ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have ha0z : a0 = 0 := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
      rw [ha0 x 0 (by simp [hne x])]
      exact MultilinearMap.map_coord_zero _ τ (by simp)
    have h1 := hz τ ⟨a0, hmem⟩ ha0
    have h0 : (⟨a0, hmem⟩ : alg O N lam) = 0 := Subtype.ext ha0z
    rw [h0, zero_smul] at h1
    exact hz0 h1.symm
  obtain ⟨x, hx⟩ := hex
  set f := weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) with hfdef
  have hfmem : f ∈ dualWeyl O N N (res N (lam τ)) := dualWeylRowGraded O N N _ _ _ (x τ).2
  have hfhom : IsWeightedHomogeneous (rowW N N) f (w τ) := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨m, hm⟩ := support_nonempty.2 hx
  have hrd : ∀ a, rowDeg m a = w τ a := fun a => by
    rw [← weight_rowW_eq_rowDeg, hfhom (mem_support_iff.1 hm)]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (∀ k : ℕ, (∑ b : Fin N with b.val < k, w τ (σ.symm b)) ≤ ∑ t : Fin N with t.val < k, res N (lam τ) t) ∧
      ∑ b : Fin N, w τ (σ.symm b) = ∑ t : Fin N, res N (lam τ) t := by
    intro σ
    let e : Fin N × Fin N → Fin N × Fin N := fun v => (σ v.1, v.2)
    have he : Function.Injective e := by
      intro u v huv
      simp only [e, Prod.mk.injEq] at huv
      exact Prod.ext (σ.injective huv.1) huv.2
    have hm' : m.mapDomain e ∈ (rename e f).support := by
      rw [mem_support_iff, coeff_rename_mapDomain e he]
      exact mem_support_iff.1 hm
    have hrd' : ∀ b, rowDeg (m.mapDomain e) b = w τ (σ.symm b) := by
      intro b
      rw [← hrd]
      unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      have : (b, s) = e (σ.symm b, s) := by simp [e]
      rw [this, Finsupp.mapDomain_apply_of_injective he]
    have hd := dualWeyl_rowDeg_dominance O N _ _ (rename_rowPerm_mem O N _ σ f hfmem) _ hm'
    simp only [hrd'] at hd
    exact hd
  have hres : ∀ t : Fin N, res N (lam τ) t = lam τ t := fun t => rfl
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · have h := (key (Equiv.refl _)).2
    simpa [hres] using h
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    obtain ⟨h1, h2⟩ := key (Equiv.swap ⟨N - 1, by omega⟩ a)
    have h3 := h1 (N - 1)
    rw [sum_fin_split_last hN, sum_fin_split_last hN] at h2
    have h4 : w τ ((Equiv.swap ⟨N - 1, by omega⟩ a).symm ⟨N - 1, by omega⟩) = w τ a := by simp
    rw [h4] at h2
    have h5 : res N (lam τ) ⟨N - 1, by omega⟩ = lam τ (N - 1) := rfl
    rw [h5] at h2
    omega
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have h1 := (key (Equiv.swap ⟨0, hN⟩ a)).1 1
    rw [sum_fin_lt_one hN, sum_fin_lt_one hN] at h1
    have h2 : w τ a ≤ res N (lam τ) ⟨0, hN⟩ := by simpa using h1
    exact h2

end GlobalTheory.HighWt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightBoundsDualWeylModuleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.jointRowWeight_bounds_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧ ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  first | exact @GlobalTheory.HighWt.jointWt_bounds | exact GlobalTheory.HighWt.jointWt_bounds | (intros; apply GlobalTheory.HighWt.jointWt_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeight

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.HighWt.simpleSubquot_embeds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam Gm _ _ hs hsub
  classical
  haveI : Nontrivial Gm := IsSimpleModule.nontrivial (alg O N lam) Gm
  obtain ⟨w0, hw0⟩ := GlobalTheory.T.exists_jointRowWeight_dualWeylModule O N ι lam Gm inferInstance
  have hB := GlobalTheory.T.jointRowWeight_bounds_dualWeylModule O N ι lam hlam Gm
  let S : Set (ι → Fin N → ℕ) := {w | GlobalTheory.HighWt.JointWt O N lam Gm w}
  have hfin : S.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun τ => Set.pi Set.univ fun _ : Fin N => Set.Iic (lam τ 0))
      fun τ => Set.Finite.pi fun _ => Set.finite_Iic _) ?_
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    intro τ a
    exact ((hB w hw τ).2 a).2
  obtain ⟨w, hwS, hmax⟩ := hfin.toFinset.exists_max_image (GlobalTheory.HighWt.pot N) ⟨w0, hfin.mem_toFinset.2 hw0⟩
  rw [Set.Finite.mem_toFinset] at hwS
  have hmax' : ∀ w', GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w :=
    fun w' h' => hmax w' (hfin.mem_toFinset.2 h')
  have hanti := GlobalTheory.T.jointRowWeight_antitone_of_maxPotential O N ι lam Gm w hwS hmax'
  refine ⟨GlobalTheory.HighWt.extW N w, fun τ => ?_, GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight O N ι lam ϖ hϖ hlam GlobalTheory.T.highest_weight_base_change (GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain O N ι lam) Gm hs hsub w hanti hwS hmax'⟩
  rw [GlobalTheory.HighWt.res_extW]
  refine ⟨hanti τ, ?_, ?_, ?_⟩
  · have := (hB w hwS τ).1
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using this
  · intro a
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using (hB w hwS τ).2 a
  · obtain ⟨a, ha, -⟩ := GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam τ (w τ)
    obtain ⟨z, hz, hfix⟩ := hwS
    let e : alg O N lam := ⟨a, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha⟩)⟩
    refine ⟨e, z, ha, ?_⟩
    rw [hfix τ e ha]
    exact hz

end
end
end
