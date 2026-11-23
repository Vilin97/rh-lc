module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Formalism.RealPlaceAnalysis.StatementB
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDualStandardRel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.HwComponentTensorDualStandard

section

@[expose] public section

open Formalism.REAL
namespace GlobalTheory

theorem hw_component_tensor_dual_standard (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))) (hEt : ∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) (hOm : ∀ y a, Om y a = ∑ c, E a c (y c)) (hy : y ≠ 0) (hw : IsHW Et θ y) (hl : Om y = lam • y) : ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a + if a = c then 1 else 0) (y c) ∧ lam = θ c + 1 - ((c : ℕ) : ℂ) + (n : ℂ) := by
  classical
  have hex : ∃ c, y c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (by ext c; simpa using h c)
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min {c | y c ≠ 0} hex
  have hlt : ∀ d, d < c → y d = 0 := fun d hd => by
    by_contra h
    exact hmin d h hd
  unfold IsHW at hw ⊢
  obtain ⟨hd, hu⟩ := hw
  have hc' : y c ≠ 0 := hc
  have hdiag : ∀ a, E a a (y c) = (θ a + if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    rw [hd a, PiLp.smul_apply] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true] at h ⊢
      rw [add_smul, one_smul, h, sub_add_cancel]
    · have hca : ¬ c = a := fun e => hac e.symm
      simp only [hac, hca, if_false, sub_zero, add_zero] at h ⊢
      exact h.symm
  refine ⟨c, hc', ⟨hdiag, ?_⟩, ?_⟩
  · intro a b hab
    have h := hEt a b y c
    rw [hu a b hab, PiLp.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simp only [if_true, hlt a hab, sub_zero] at h
      exact h.symm
    · simp only [hcb, if_false, sub_zero] at h
      exact h.symm
  · have h := hOm y c
    rw [hl, PiLp.smul_apply] at h
    have hterm : ∀ d, E c d (y d) =
        ((if d = c then θ c + 1 else 0) + (if c < d then (1 : ℂ) else 0)) • y c := by
      intro d
      rcases lt_trichotomy d c with hdc | hdc | hdc
      · simp [hlt d hdc, hdc.ne, hdc.not_gt]
      · subst hdc
        simp [hdiag d]
      · have h2 := hEt c d y d
        rw [hu c d hdc, PiLp.zero_apply] at h2
        simp only [if_true] at h2
        have h3 := (sub_eq_zero.mp h2.symm)
        simp [h3, hdc, hdc.ne']
    simp_rw [hterm] at h
    rw [← Finset.sum_smul] at h
    have h4 := smul_left_injective ℂ hc' h
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_boole] at h4
    have h5 : (Finset.univ.filter (fun d : Fin (n + 1) => c < d)).card = n - c := by
      have : Finset.univ.filter (fun d : Fin (n + 1) => c < d) = Finset.Ioi c := by
        ext d; simp
      rw [this, Fin.card_Ioi]; omega
    rw [h5, Nat.cast_sub (Nat.lt_succ_iff.mp c.2)] at h4
    rw [h4]; ring
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleDualStandard

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem casimir_eigenspace_irred_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  intro V _ _ _ n E Et Om β L l hH hA hEt hOm
  classical
  obtain ⟨hgl, hAt, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hH.gl hA hEt hOm
  set S := Module.End.eigenspace Om (β + L l + (n : ℂ)) with hS
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    have := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hdec : SDec (shf β L) := by
    intro a b hab
    have h := hH.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by exact_mod_cast h2
    rw [h3]; simp only [shf]; ring
  have hwt : ∀ (ν : Fin (n + 1) → ℂ) (v : V), v ≠ 0 → IsHW E ν v →
      ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hm : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => hH.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h => hv (by rw [h] at hm; simpa using hm)
    exact (Formalism.FourierDecayAlt.P.capelli_singular V (n + 1) E _ hH.gl hne).2 hdec ν v hm hv hw j
  have hkey : ∀ (θ : Fin (n + 1) → ℂ) (y : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 →
      IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) - if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    rw [hS, Module.End.mem_eigenspace_iff] at hy
    obtain ⟨c, hc, hwc, hlam⟩ :=
      hw_component_tensor_dual_standard V n E Et Om θ _ y hEt hOm hy0 hw hy
    have h1 := hwt _ _ hc hwc
    have h2 := h1 c
    simp only [if_true] at h2
    have h3 : (L l : ℂ) = L c := by linear_combination hlam + h2
    have h4 : l = c := hH.anti.injective (by exact_mod_cast h3)
    subst h4
    refine ⟨hc, ?_, ?_⟩
    · have : (fun j => β + L j + ((j : ℕ) : ℂ)) = fun a => θ a + if a = l then 1 else 0 :=
        funext fun j => (h1 j).symm
      rw [this]; exact hwc
    · funext j
      rw [← h1 j]; ring
  have hsub : ∀ (ν : Fin (n + 1) → ℂ) (v : V), IsHW E ν v →
      IsHW (subA E) (fun a => ν a.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
  have hprop : ∀ (θ θ' : Fin (n + 1) → ℂ) (y y' : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S →
      y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y := by
    intro θ θ' y y' hy hy0 hw hy' hy0' hw'
    obtain ⟨a1, a2, a3⟩ := hkey θ y hy hy0 hw
    obtain ⟨b1, b2, b3⟩ := hkey θ' y' hy' hy0' hw'
    obtain ⟨t, ht⟩ := Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hH.gl hH.irr (hsub _ _ a2)
      (hsub _ _ b2) a1
    refine ⟨t, ?_⟩
    by_contra hne
    have hθ : θ' = θ := b3.trans a3.symm
    rw [hθ] at hw'
    have hz : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab, smul_zero, sub_zero]
    have := (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) (sub_ne_zero.mpr hne) hz).1
    apply this
    rw [PiLp.sub_apply, PiLp.smul_apply, ht, sub_self]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hT : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at this
      exact h1 this
    have hTs : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hAt]
      exact hv1 _ (hst b a u hu)
    obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S' hst h0
    obtain ⟨θ', y', hy', hy0', hw', -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl _ hTs hT
    obtain ⟨t, ht⟩ := hprop θ θ' y y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hm : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hm2 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hm2 y' hm))
  refine ⟨hstab, hirr, ?_⟩
  by_cases h0 : S = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
    Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S hstab h0
  obtain ⟨-, -, hθ⟩ := hkey θ y hy hy0 hw
  have hcap : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ (n + 1) Et θ y hgl hw w]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hθ]
    by_cases hk : k = l
    · subst hk
      simp only [if_true, Function.update_self]
      push_cast; ring
    · simp only [hk, if_false, Function.update_of_ne hk]
      ring
  have hcs := (Formalism.FourierDecayAlt.P.capelli_stabilizer _ (n + 1) Et
    (shf β (Function.update L l (L l - 1))) hgl).1
  rcases hirr (CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S) inf_le_right
    (fun a b v hv => ⟨hcs a b v hv.1, hstab a b v hv.2⟩) with h | h
  · have : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S := ⟨hcap, hy⟩
    rw [h] at this
    exact absurd (by simpa using this) hy0
  · exact inf_eq_right.mp h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleDualStandardStatement

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.splitCasimir_eigenspace_irreducible_dualStandard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  first | exact @GlobalTheory.casimir_eigenspace_irred_dual_standard | exact GlobalTheory.casimir_eigenspace_irred_dual_standard | (intros; apply GlobalTheory.casimir_eigenspace_irred_dual_standard <;> assumption)
end
end
