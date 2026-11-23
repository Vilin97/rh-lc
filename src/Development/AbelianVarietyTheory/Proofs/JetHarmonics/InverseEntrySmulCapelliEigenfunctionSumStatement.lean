module

public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliModuleModel
public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDetVectorMultiplierShiftPlus
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovectorMultiplierShift

section

@[expose] public section

open Formalism.REAL Finset

namespace GlobalTheory


open Finset in
theorem _root_.GlobalTheory.covector_multiplier_shift : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), _root_.Formalism.REAL.qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b - if a = j then x b else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), _root_.Formalism.REAL.qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t - if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  obtain ⟨hF, hqF⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  obtain ⟨hF', hqF'⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'
  have hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w) := by
    intro a b w
    simp only [LinearMap.neg_apply, map_neg, hι]
  have hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s) := by
    intro s t h
    apply hν
    have h' : (1 - n - ν s : ℂ) = 1 - n - ν t := h
    linear_combination -h'
  have hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w
      = (∏ s, (u + (1 - n - ν s))) • w := by
    intro u w
    rw [hqF', LinearMap.smul_apply, hq, smul_smul]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0 := by
    intro a b k
    rw [neg_mul, mul_neg, hx b a k]
    abel
  obtain ⟨v, hv1, hv2⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a)
    (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w
  · refine ⟨v, hv1, fun s u => ?_⟩
    have h := hv2 s ((n : ℂ) - 1 - u)
    rw [hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply] at h
    have h2 := congrArg (((-1 : ℂ) ^ n) • ·) h
    simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2
    rw [h2]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.EhInvEntry

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Matrix in
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSum

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_inv_entry (k r : ℕ) (c j : Fin (2 * r + k + 1)) :
    B.CkOn ⊤ (B.GV k r) (fun y : B.Mat k r => y⁻¹ c j) := by
  intro g₀ _
  refine ⟨Set.univ, fun g => Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c g, isOpen_univ, trivial,
    (Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c).contDiff.contDiffOn, fun g _ hg => ?_⟩
  show g⁻¹ c j = Matrix.mulVec (Hpk k r * g.conjTranspose * Hpk k r) (Pi.single j 1) c
  rw [← Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp

theorem inCC_inv_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (c j : Fin (2 * r + k + 1)) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A m F) :
    B.InCC (A - 1) m (fun g : B.Mat k r => g⁻¹ c j • F g) := by
  have hg : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => g⁻¹ c j) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_congr (fun g _ => by simp)
      (Formalism.FourierDecayAlt.P.JCx2.pd_good_inv (Wp := Wp) (Wq := Wq) (Pi.single j 1) c)
  obtain ⟨K, -, hK⟩ := hg.2 (A - 1) m
  obtain ⟨b, hb⟩ := hF
  exact ⟨K * b, hK F b (by rw [Nat.cast_one, sub_add_cancel]; exact hb)⟩

theorem inv_entry_smul_eigen_split : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  intro k r Wp Wq _ _ _ _ _ _ lam A i j f hlam hf heig
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hE, hE', hι, hq, hsm, hext, hcc, hex, -, hqC, hmul⟩ :=
    GlobalTheory.capelli_module_model k r Wp Wq lam A
  obtain ⟨w, hw⟩ := hex f hf heig
  let x : Fin (2 * r + k + 1) → Module.End ℂ V := fun c => mul (fun y : B.Mat k r => y⁻¹ c j)
  have hx : ∀ c v, ∀ g ∈ B.GV k r, ev (x c v) g = g⁻¹ c j • ev v g :=
    fun c => (hmul _ (ckOn_inv_entry k r c j)).1
  have hcomm : ∀ a b c, E a b * x c = x c * E a b - if a = c then x b else 0 := by
    intro a b c
    ext v
    refine hext _ _ fun g hg => ?_
    have h1 := (hmul _ (ckOn_inv_entry k r c j)).2 a b v g hg
    rw [GlobalTheory.eh_inv_entry k r a b c j g hg] at h1
    rw [Module.End.mul_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.mul_apply, hx _ _ g hg]
    refine h1.trans ?_
    split_ifs with h
    · rw [hx _ _ g hg, neg_smul, sub_eq_add_neg]
    · simp
  have hinj : Function.Injective
      (fun s => ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2)) := by
    intro s t h
    apply hlam
    have h' : (lam s : ℂ) = lam t := sub_left_inj.1 h
    exact_mod_cast h'
  obtain ⟨v, hv1, hv2⟩ := GlobalTheory.covector_multiplier_shift V W _ E E' ι x _ hE hE' hι hinj hq hcomm i w
  refine ⟨fun t => ev (∑ a, x a (ι (v t a))), fun t => ⟨hsm _, fun m => ?_⟩, fun t Y g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum (A := A - 1) (m := m) Finset.univ
      (fun a (g : B.Mat k r) => g⁻¹ a j • ev (ι (v t a)) g)
      (fun a _ => inCC_inv_entry_smul a j (hcc (v t a) m))
    refine ⟨b, Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => ?_) hb⟩
    beta_reduce

    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hx _ _ g hg).symm
  · rw [← hqC _ _ g hg, hv2, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> ring

  · rw [← hw g hg, ← hx i _ g hg, hv1, map_sum, Finset.sum_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSumStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  first | exact @GlobalTheory.inv_entry_smul_eigen_split | exact GlobalTheory.inv_entry_smul_eigen_split | (intros; apply GlobalTheory.inv_entry_smul_eigen_split <;> assumption)
end
end
