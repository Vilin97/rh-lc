module

public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
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
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ColumnsPieriSkeleton
public import Formalism.PieriBlockIdeals.PieriColumnMinors.IrreducibleGeneration
public import Formalism.PieriBlockIdeals.PieriColumnMinors.XiOfDepth2
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
public import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LowerTriangularIntegral
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LriEVPowCoe
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds

-- Source module: Formalism.PieriBlockIdeals.StatementDown

section

@[expose] public section

noncomputable section

namespace Formalism.CohomologicalDescent.Down

section SLD

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD

section SLD2

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD2

section SF06

open CategoryTheory CategoryTheory.Limits
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

end SF06

section SF07

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative

end SF07

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def InclWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l

end SF09

end Formalism.CohomologicalDescent.Down
end
end
end

-- Source module: Formalism.PieriBlockIdeals.PieriColumnMinors.LrjTransposeLift

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lrj_liftWord_cons (p : ℕ) {q : ℕ} (x : Fin q × Fin q × ℕ) (ω : List (Fin q × Fin q × ℕ)) :
    liftWord p (x :: ω) = (Fin.natAdd p x.1, Fin.natAdd p x.2.1, x.2.2) :: liftWord p ω := rfl

theorem lrj_transpose_lift (p : ℕ) {q : ℕ} (ω : List (Fin q × Fin q × ℕ)) :
    transposeWord (liftWord p (transposeWord ω)) = liftWord p ω := by
  simp [transposeWord, liftWord, List.map_reverse, List.map_map, Function.comp_def]

theorem levZ_sub (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (hf : f ∈ LevZ p q w lam2) :
    ∃ y : (rationalBlockModuleSetting p q w lam2).W, ((y : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = f := by
  let M : Submodule ℚ (MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) :=
    (W0 p q w lam2).map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype
  have hM : ∀ (b b' : Fin q) (k : ℕ), ∀ g ∈ M, rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k g ∈ M := by
    intro b b' k
    refine closed_of_der _ _ M ?_ k
    rintro g ⟨x, hx, rfl⟩
    exact ⟨EV p q w lam2 (Sum.inr b) (Sum.inr b') x, w_zero_stable_right_block p q w lam2 b b' x hx, rfl⟩
  have hgen : ∀ ω : List (Fin q × Fin q × ℕ), applyWord ℚ (liftWord p ω) (hw ℚ le_rfl (LD.blockWt p q w lam2)) ∈ M := by
    intro ω
    induction ω with
    | nil => exact ⟨hwV p q w lam2 ha hb, hwV_mem p q w lam2 ha hb, rfl⟩
    | cons x ω ih =>
      rw [lrj_liftWord_cons, applyWord_cons]
      exact hM _ _ _ _ ih
  have hle : LevZ p q w lam2 ≤ M.restrictScalars ℤ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ω, rfl⟩
    exact hgen ω
  obtain ⟨x, hx, hxf⟩ := hle hf
  exact ⟨⟨x, hx⟩, hxf⟩

theorem resInj (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (z : VQ p q w lam2) (hz : z ∈ W0 p q w lam2)
    (h0 : res ℚ p q (z : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0) : z = 0 := by
  let Z : Submodule ℚ (VQ p q w lam2) :=
    W0 p q w lam2 ⊓ LinearMap.ker ((res ℚ p q).toLinearMap.comp
      (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype)
  have hst : ∀ b b' : Fin q, ∀ u ∈ Z, EV p q w lam2 (Sum.inr b) (Sum.inr b') u ∈ Z := by
    rintro b b' u ⟨huW, huk⟩
    have huk' : res ℚ p q (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0 := huk
    refine ⟨w_zero_stable_right_block p q w lam2 b b' u huW, ?_⟩
    show res ℚ p q ((EV p q w lam2 (Sum.inr b) (Sum.inr b') u : VQ p q w lam2) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
    rw [EV_coe]
    show res ℚ p q (der (p + q) (p + q) (Fin.natAdd p b) (Fin.natAdd p b') u) = 0
    rw [← rowDiv_one, res_rowDiv, huk']
    simp [rowDiv]
  by_contra hne
  have hZ : Z ≠ ⊥ := by
    intro hb0
    have : z ∈ Z := ⟨hz, h0⟩
    rw [hb0, Submodule.mem_bot] at this
    exact hne this
  have hh := real_irreducible p q w lam2 ha hb Z inf_le_left hst hZ (hwV p q w lam2 ha hb) rfl
  have : res ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2)) = 0 := hh.2
  rw [res_hw p q w lam2 ha hb] at this
  exact hwNe ℚ q q le_rfl lam2 this

theorem wt_extract (p q w : ℕ) (lam2 : Fin q → ℕ) (u : VQ p q w lam2) (hu : u ≠ 0) (κ : Fin p ⊕ Fin q → ℤ)
    (hw' : u ∈ (rationalBlockModuleSetting p q w lam2).wt κ) :
    ∃ μN : Fin (p + q) → ℕ, IsWeightedHomogeneous (rowW (p + q) (p + q))
      (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) μN ∧ κ = fun a => (μN (idx p q a) : ℤ) := by
  have hu' : (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ≠ 0 := fun h => hu (Subtype.ext h)
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hu'
  rw [MvPolynomial.mem_support_iff] at hd
  have hκ : κ = fun a => ((Finsupp.weight (rowW (p + q) (p + q)) d (idx p q a) : ℕ) : ℤ) := by
    funext a
    have h1 := congrArg (fun x : VQ p q w lam2 => AddMonoidAlgebra.coeff (x : MvPolynomial _ ℚ) d) (((mem_wt p q w lam2 u κ).1 hw') a)
    simp only [EV_coe, coeff_der_diag, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    exact_mod_cast h2.symm
  refine ⟨Finsupp.weight (rowW (p + q) (p + q)) d, ?_, hκ⟩
  rw [hκ] at hw'
  exact (real_weight p q w lam2 u _).2 hw'

theorem liftWeyl (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (y : MvPolynomial (Fin q × Fin q) ℤ) (hy : y ∈ weyl ℤ q q le_rfl lam2) :
    ∃ d ∈ LevZ p q w lam2, res ℚ p q d = intQ q q y := by
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    refine ⟨applyWord ℚ (liftWord p ω) (hw ℚ le_rfl (LD.blockWt p q w lam2)), Submodule.subset_span ⟨ω, rfl⟩, ?_⟩
    rw [res_applyWord, res_hw p q w lam2 ha hb, lrc_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, e1⟩ := hx
    obtain ⟨d2, h2, e2⟩ := hy
    exact ⟨d1 + d2, Submodule.add_mem _ h1 h2, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨d1, h1, e1⟩ := hx
    exact ⟨c • d1, Submodule.smul_mem _ c h1, by rw [map_zsmul, map_zsmul, e1]⟩

theorem lrj_hom_of_smul {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (g' : MvPolynomial σ ℤ) (g : MvPolynomial σ ℚ)
    (m : ℤ) (μ : M) (hg : IsWeightedHomogeneous wt g μ) (h : (m : ℚ) • g = map (Int.castRingHom ℚ) g') :
    IsWeightedHomogeneous wt g' μ := by
  intro d hd
  apply hg
  intro h0
  apply hd
  have h1 := congrArg (AddMonoidAlgebra.coeff · d) h
  rw [MvPolynomial.coeff_smul, h0, smul_zero, coeff_map] at h1
  have h2 : ((AddMonoidAlgebra.coeff g' d : ℤ) : ℚ) = 0 := by simpa using h1.symm
  exact_mod_cast h2

theorem expL_real (hC : CoeffWord) (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2)
    (hb : ∀ b, lam2 b ≤ w) (ξ : Fin (p + q) → ℤ) (i' : ℤ) (eL : ℕ)
    (heL : ∀ μ2 : Fin q → ℕ, LD.depth2 ξ (LD.blockWt p q w lam2) (LD.blockWt p q w μ2) ≤ i' →
      LD.ExpLe l q lam2 μ2 eL) :
    ∀ κ, xiOf ξ (lamOf p q w lam2 - κ) ≤ i' →
      ∀ u ∈ NablaL (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) (DelLR l hl p q w lam2),
      ((u : VQ p q w lam2)) ∈ (rationalBlockModuleSetting p q w lam2).wt κ → ((l : Zl l) ^ eL) • u ∈ DelLR l hl p q w lam2 := by
  intro κ hκ u hu hwt
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  by_cases hu0 : u = 0
  · rw [hu0, smul_zero]; exact Submodule.zero_mem _
  have hu0' : (u : VQ p q w lam2) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨μN, hμN, rfl⟩ := wt_extract p q w lam2 _ hu0' κ hwt
  have huW : (u : VQ p q w lam2) ∈ W0 p q w lam2 := u.2
  have hfirst : ∀ α : Fin p, μN (Fin.castAdd q α) = w := by
    intro α
    have h1 := ((mem_orthogonal_frame_iff p q w lam2 _).1 huW).2 α α
    have h2 := ((mem_wt p q w lam2 _ _).1 hwt) (Sum.inl α)
    rw [if_pos rfl, h2] at h1
    have h3 := smul_left_injective ℚ hu0' h1
    exact_mod_cast h3
  let μ2 : Fin q → ℕ := fun b => μN (Fin.natAdd p b)
  have hblock : LD.blockWt p q w μ2 = μN := by
    funext a
    refine Fin.addCases (fun α => ?_) (fun b => ?_) a
    · rw [LD.blockWt, Fin.append_left, hfirst]
    · rw [LD.blockWt, Fin.append_right]
  have hd : LD.depth2 ξ (LD.blockWt p q w lam2) (LD.blockWt p q w μ2) ≤ i' := by
    rw [hblock]
    calc LD.depth2 ξ (LD.blockWt p q w lam2) μN = _ := (xiOf_depth2 ξ (LD.blockWt p q w lam2) μN).symm
      _ ≤ i' := hκ
  set f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ :=
    ((u : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) with hf
  have hfN : f ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2) := (u : VQ p q w lam2).2
  have hg := res_mem ℚ p q w lam2 f hfN
  have hω : ∀ ω : List (Fin q × Fin q × ℕ), eval (idFrame ℚ q q) (applyWord ℚ ω (res ℚ p q f)) ∈ Zl l := by
    intro ω
    obtain ⟨y, hy⟩ := levZ_sub p q w lam2 ha hb _ (Submodule.subset_span ⟨transposeWord ω, rfl⟩)
    have hyD : y ∈ DelLR l hl p q w lam2 := le_locSpan _ _ _ ((mem_MW p q w lam2 y).2 (by
      rw [hy]; exact Submodule.subset_span ⟨transposeWord ω, rfl⟩))
    have h1 := hu y hyD
    rw [mem_one_iff] at h1
    have e1 : (formB p q w lam2).restrict (rationalBlockModuleSetting p q w lam2).W u y =
        formB p q w lam2 (u : VQ p q w lam2) (y : VQ p q w lam2) := rfl
    rw [e1, formB_apply, hy, fock_word _ _ hanti _ hfN, lrj_transpose_lift,
      mul_div_assoc, div_self (ne_of_gt (hw_norm_pos _)), mul_one, ← res_eval_id ℚ p q, res_applyWord] at h1
    exact h1
  obtain ⟨m, hm, g', hg', hmg⟩ := dual_int_loc hC lower_triangular_integral l hl q lam2 _ hg hω
  have hg'h : IsWeightedHomogeneous (rowW q q) g' μ2 :=
    lrj_hom_of_smul _ g' _ m μ2 (res_rowHom ℚ p q μN f hμN) (by rw [hmg, lrc_intQ_apply])
  obtain ⟨m', hm', hy'⟩ := heL μ2 hd g' ⟨hg', hg'h⟩
  obtain ⟨d, hdL, hdres⟩ := liftWeyl p q w lam2 ha hb _ hy'
  obtain ⟨yd, hyd⟩ := levZ_sub p q w lam2 ha hb d hdL
  set c : ℤ := m' * (l : ℤ) ^ eL * m with hc
  let zW : (rationalBlockModuleSetting p q w lam2).W := (c : ℚ) • u - yd
  have hz : (zW : VQ p q w lam2) = 0 := by
    refine resInj p q w lam2 ha hb _ zW.2 ?_
    show res ℚ p q ((((c : ℚ) • u - yd : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) : MvPolynomial _ ℚ) = 0
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
    rw [hyd, hdres, map_zsmul, ← hmg, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, sub_eq_zero, hc]
    congr 1
    push_cast
    ring
  have hz2 : zW = 0 := Subtype.ext hz
  have hcu : (c : ℚ) • u = yd := sub_eq_zero.mp hz2
  rw [DelLR, mem_locSpan]
  refine ⟨m' * m, ?_, ?_⟩
  · intro h
    rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h | h
    · exact hm' h
    · exact hm h
  · rw [← Int.cast_smul_eq_zsmul ℚ, lrc_smul_def, smul_smul]
    have hsc : ((m' * m : ℤ) : ℚ) * (((l : Zl l) ^ eL : Zl l) : ℚ) = (c : ℚ) := by
      simp [hc]
      ring
    rw [hsc, hcu]
    exact (mem_MW p q w lam2 yd).2 (by rw [hyd]; exact hdL)

end Formalism.CohomologicalDescent.LR
end
end
end

-- Source module: Formalism.PieriBlockIdeals.PieriColumnMinors.RealOfSkeleton

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem levZ_rowDiv (p q w : ℕ) (lam2 : Fin q → ℕ) (b b' : Fin q) (k : ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (hf : f ∈ LevZ p q w lam2) :
    rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k f ∈ LevZ p q w lam2 := by
  unfold LevZ at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    exact Submodule.subset_span ⟨(b, b', k) :: ω, rfl⟩
  | zero => simpa [rowDiv] using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k (c • x) =
        c • rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k x :=
      map_zsmul (rowDivL ℚ (n := p + q) (Fin.natAdd p b) (Fin.natAdd p b') k) c x
    rw [e]
    exact Submodule.smul_mem _ c hx

theorem delL_stable (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (b b' : Fin q)
    (u : (rationalBlockModuleSetting p q w lam2).W) (hu : u ∈ DelLR l hl p q w lam2) :
    (rationalBlockModuleSetting p q w lam2).EW b b' u ∈ DelLR l hl p q w lam2 := by
  obtain ⟨m, hm, hmu⟩ := (mem_locSpan _ _ _ _).1 hu
  refine (mem_locSpan _ _ _ _).2 ⟨m, hm, ?_⟩
  rw [← map_zsmul]
  rw [mem_MW] at hmu ⊢
  have e : ((((rationalBlockModuleSetting p q w lam2).EW b b' (m • u) : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') 1 (((m • u : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) :
        MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) := by
    rw [rowDiv_one]
    rfl
  rw [e]
  exact levZ_rowDiv p q w lam2 b b' 1 _ hmu

theorem real_of_skeleton : RealOfSkeleton := by
  intro hC _hL hP hCol l p q w lam2 ξ hl ha hb hξ i' eL heL i μ hd hd2 x hx
  obtain ⟨hxN, hxμ⟩ := hx
  rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule] at hxμ
  have hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2) := by
    rw [lrc_intQ_apply]
    exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) _ _ _ x hxN
  have inputs : LemmaDInputs3 (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) i w lam2 (DelLR l hl p q w lam2)
      (xiOf ξ) (lamOf p q w lam2) (l : Zl l) eL i' :=
    { scalar := rfl
      le_w := hb
      contra := real_contragredient p q w lam2
      generated := real_generated p q w lam2 ha hb
      nondeg := real_nondegenerate p q w lam2
      stable := delL_stable l hl p q w lam2
      pieri := hP p q w lam2 ha hb i
      columns := fun tau htau => hCol p q w lam2 ha hb i tau (by simpa using htau)
      dominant := dominant_xi ξ hξ
      expL := expL_real hC l hl p q w lam2 ha hb ξ i' eL heL }
  have hdep : ∑ α : Fin p, (fun a => ((μ (idx p q a) : ℕ) : ℤ)) (Sum.inl α) + (i : ℤ) =
      (Fintype.card (Fin p) : ℤ) * (w : ℤ) := by
    simp only [Fintype.card_fin]
    have := hd
    unfold LD.IsDepth at this
    exact_mod_cast this
  have hxi : xiOf ξ (lamOf p q w lam2 - fun a => ((μ (idx p q a) : ℕ) : ℤ)) ≤ i' :=
    calc xiOf ξ (lamOf p q w lam2 - fun a => ((μ (idx p q a) : ℕ) : ℤ)) = LD.depth2 ξ (LD.blockWt p q w lam2) μ :=
          xiOf_depth2 ξ _ μ
      _ ≤ i' := hd2
  have h := depth_skeleton_third_form_holds (Zl l) ℚ (VQ p q w lam2) (Fin p) q (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) i w
    lam2 (DelLR l hl p q w lam2) (xiOf ξ) (lamOf p q w lam2) l eL i' hl (zl_unit hl) inputs
    (fun a => ((μ (idx p q a) : ℕ) : ℤ)) hdep hxi ⟨intQ _ _ x, hx'⟩ (mem_dual l hl p q w lam2 ha hb x hxN hx')
    (wt_of_hom p q w lam2 x hx' μ hxμ)
  rw [Fintype.card_fin] at h
  exact concl l hl p q w lam2 x hx' _ h.1

theorem real_of_pieri : RealOfPieri :=
  fun hP hCol => real_of_skeleton coefficient_word lower_triangular_integral hP hCol

end Formalism.CohomologicalDescent.LR
end
end
end

-- Source module: Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsLinkage

section

@[expose] public section

namespace Formalism.CohomologicalDescent.Down

theorem hG : LD.LemmaDGraded :=
  LR.real_of_pieri LPR.pieri_real_form (ColumnMinorsFromPieri.columns_real_of_pieri_real LPR.pieri_real_form)

theorem inclusion_w_real_holds : InclWReal := ShortWeightBounds.inclusion_w_real_holds hG

end Formalism.CohomologicalDescent.Down
end
end
