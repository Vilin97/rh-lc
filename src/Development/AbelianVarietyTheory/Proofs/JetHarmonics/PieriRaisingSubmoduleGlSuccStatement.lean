module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandardStatement
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
public import Formalism.RealPlaceAnalysis.StatementE
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimirStatement

section

@[expose] public section

open Formalism.REAL

theorem _root_.GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  first | exact @GlobalTheory.comatrix_last_row_inverts_casimir | exact GlobalTheory.comatrix_last_row_inverts_casimir | (intros; apply GlobalTheory.comatrix_last_row_inverts_casimir <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirStdEigenvalue

section

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLast

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLastStatement

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.starProjection_splitCasimir_raising_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.starProjection_splitCasimirStd_last | exact GlobalTheory.starProjection_splitCasimirStd_last | (intros; apply GlobalTheory.starProjection_splitCasimirStd_last <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSucc

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory.WigSh

theorem exists_splitCasimir_std (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]

theorem pieri_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hyp hadj hEt hL
  obtain ⟨Om, hOm⟩ := exists_splitCasimir_std V n E
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt V n E Et Om β L l hyp hadj hEt hOm
  have h4 := GlobalTheory.T.starProjection_splitCasimir_raising_last V n E Et Om β L l hyp hadj hEt hOm
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.castSucc) := fun j =>
    ⟨hyp.anti (Fin.castSucc_lt_succ), le_rfl⟩
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hyp).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hyp.anti).1 hL
  have hmem := Submodule.starProjection_apply_mem (Module.End.eigenspace Om (β + L l + 0))
    (PiLp.single 2 (Fin.last n) v)
  have hz : (Module.End.eigenspace Om (β + L l + 0)).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := (Submodule.eq_bot_iff _).1 hbot _ hmem
  rw [hz] at h5
  have h6 : ((wP L (fun j : Fin n => L j.castSucc) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSuccStatement

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.pieri_raising_submodule_glSucc : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.pieri_step_raise | exact GlobalTheory.WigSh.pieri_step_raise | (intros; apply GlobalTheory.WigSh.pieri_step_raise <;> assumption)
end
end
