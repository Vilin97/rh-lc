module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoeffB
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Entries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FinPartMulVec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.MixApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StepInv
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ProdEntries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuaternaryFormEqOfFinitePart
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkStab

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkStab :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (T : Module.End ℂ (S4 F)) (N N' : Submodule ℂ (S4 F)), N' ≤ Vac δ → (∀ φ ∈ N, T φ ∈ N') →
    (∀ w i φ, T (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)}) → ∀ m, ∀ φ ∈ O.Fk N m, T φ ∈ O.Fk N' m := by
  intro F _ _ _ δ O T N N' hN' hN hT m
  induction m with
  | zero => exact hN
  | succ m ih =>
    have hb := fkBasic F O
    have hmono : O.Fk N' m ≤ O.Fk N' (m + 1) := hb.1 N' N' le_rfl m (m + 1) (Nat.le_succ m)
    have key : O.Fk N (m + 1) ≤ (O.Fk N' (m + 1)).comap T := by
      have hu : O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := rfl
      rw [hu]
      refine sup_le (fun φ hφ => hmono (ih φ hφ)) (iSup_le fun w => iSup_le fun i => ?_)
      rintro _ ⟨φ, hφ, rfl⟩
      have hs : Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)} ≤ O.Fk N' (m + 1) := by
        refine Submodule.span_le.2 ?_
        rintro χ ⟨w', j, rfl | rfl⟩
        · exact hb.2.1 N' m w' j _ (ih φ hφ)
        · exact fkD F δ O N' hN' m w' j _ (ih φ hφ)
      exact hs (hT w i φ)
    exact fun φ hφ => key hφ
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmFinite

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omFinite :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)), IsCompact C → ∃ s : Set (G1 F), s.Finite ∧ (∀ g ∈ s, InfOne g) ∧
    ∀ k ∈ C, ∃ g ∈ s, ∃ k', FinOne k' ∧ (InfOrth k → InfOrth k') ∧ W.Om k φ = W.Om k' (W.Om g φ) := by
  intro F E _ _ _ _ _ _ _ D W φ C hC
  obtain ⟨pi, pf, hpf, hp⟩ := UpperTheory.ConvolutionTheory.R2.Fo.proj F
  have hU : ∀ k₀ ∈ C, {k | W.Om (pf k) φ = W.Om (pf k₀) φ} ∈ 𝓝 k₀ := by
    intro k₀ _
    have hc : Continuous fun k : G1 F => pf (k₀⁻¹ * k) :=
      hpf.comp (continuous_const.mul continuous_id)
    have h1 : Tendsto (fun k : G1 F => pf (k₀⁻¹ * k)) (𝓝 k₀) (𝓝 1) := by
      have h := hc.tendsto k₀
      simpa using h
    filter_upwards [h1.eventually (W.level φ)] with k hk
    have h2 := hk (hp _).2.1
    have h3 : pf k = pf k₀ * pf (k₀⁻¹ * k) := by rw [← map_mul, mul_inv_cancel_left]
    change W.Om (pf k) φ = W.Om (pf k₀) φ
    rw [h3, map_mul, Module.End.mul_apply, h2]
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover _ hU
  refine ⟨pf '' (t : Set (G1 F)), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact (hp k).2.1
  · intro k hk
    obtain ⟨k₀, hk₀, hkk⟩ := Set.mem_iUnion₂.1 (hcov hk)
    refine ⟨pf k₀, ⟨k₀, hk₀, rfl⟩, pi k, (hp k).1, ?_, ?_⟩
    · intro ho i j
      have e : ∀ a b, ((pi k).1 a b).1 = (k.1 a b).1 := (hp k).2.2.2.1
      have key : (((pi k).1 * (pi k).1ᵀ) i j).1 = ((k.1 * k.1ᵀ) i j).1 := by
        have hadd : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
        rw [hadd, hadd, e i 0, e j 0, e i 1, e j 1]
      exact key.trans (ho i j)
    · have h4 : W.Om k = W.Om (pi k) * W.Om (pf k) := by rw [← map_mul, (hp k).2.2.1]
      rw [h4, Module.End.mul_apply]
      exact congrArg _ hkk
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmX

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (g : G1 F) w i φ, W.Om g (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.Om g φ) ∨ χ = O.d w' j (W.Om g φ)} := by
  intro F E _ _ _ _ _ _ _ D W O g w i φ
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hδ : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have key : ∀ i : Fin 4, ∃ (j : Fin 4) (c : ℂ), c ≠ 0 ∧ O.p D.δ w j = c • O.x w i := by
    intro i
    fin_cases i
    · exact ⟨1, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨0, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨2, 2 * cc, mul_ne_zero two_ne_zero hcc, rfl⟩
    · exact ⟨3, -2 * cw w (rt D.δ) * cc,
        mul_ne_zero (mul_ne_zero (neg_ne_zero.2 two_ne_zero) hδ) hcc, rfl⟩
  obtain ⟨j, c, hc, hp⟩ := key i
  have h := (Heisenberg₂ F E D W O g⁻¹ w j).2
  have h1 : W.Om g * W.Om g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : W.Om g⁻¹ * W.Om g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  generalize cw w (g⁻¹ 1 0) = α at h
  generalize cw w (g⁻¹ 1 1) = β at h
  have h2 : W.Om g * O.p D.δ w j = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by
    calc W.Om g * O.p D.δ w j = W.Om g * O.p D.δ w j * (W.Om g⁻¹ * W.Om g) := by rw [h3, mul_one]
      _ = W.Om g * (O.p D.δ w j * W.Om g⁻¹) * W.Om g := by simp only [mul_assoc]
      _ = W.Om g * (W.Om g⁻¹ * (α • O.d w j + β • O.p D.δ w j)) * W.Om g := by rw [h]
      _ = (W.Om g * W.Om g⁻¹) * (α • O.d w j + β • O.p D.δ w j) * W.Om g := by simp only [mul_assoc]
      _ = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by rw [h1, one_mul]
  have hx : O.x w i = c⁻¹ • O.p D.δ w j := by rw [hp, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h4 : W.Om g (O.p D.δ w j φ) = α • O.d w j (W.Om g φ) + (β * c) • O.x w i (W.Om g φ) := by
    have := LinearMap.congr_fun h2 φ
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at this
    rw [this, hp, LinearMap.smul_apply, smul_smul]
  have h5 : W.Om g (O.x w i φ) =
      (c⁻¹ * α) • O.d w j (W.Om g φ) + (c⁻¹ * (β * c)) • O.x w i (W.Om g φ) := by
    rw [hx, LinearMap.smul_apply, map_smul, h4, ← hx, smul_add, smul_smul, smul_smul]
  rw [h5]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inr rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, i, Or.inl rfl⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.fockSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.FockSt W := by
  intro F E _ _ _ _ _ _ _ D W
  obtain ⟨O⟩ := opsEx F
  have one : ∀ (T : Module.End ℂ (S4 F)), (∀ φ ∈ Vac D.δ, T φ ∈ Vac D.δ) →
      (∀ w i φ, T (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)}) → ∀ φ ∈ Fock D.δ, T φ ∈ Fock D.δ := by
    intro T h1 h2 φ hφ
    obtain ⟨Λ, m, hm⟩ := fockEx F E D O {φ} (Set.finite_singleton φ) (by simpa using hφ)
    exact (fkLe F D.δ O).2 _ le_rfl m (fkStab F D.δ O T (Vac D.δ ⊓ Fix D.δ Λ) _ le_rfl (fun χ hχ => h1 χ hχ.1) h2 m φ (hm φ rfl))
  refine ⟨fun k => one _ (vacL F E D W _ ?_) (lX F E D W O _), fun φ hφ => ?_, fun φ hφ C hC hO => ?_⟩
  · rw [pInf_finGL]; exact one_mem _
  · obtain ⟨Λ, m, hm⟩ := fockEx F E D O {φ} (Set.finite_singleton φ) (by simpa using hφ)
    refine ⟨_, (fkLe F D.δ O).2 _ inf_le_left m, (fkBasic F O).2.2 _ (vacFd F E D Λ) m, fun k => ?_⟩
    refine fkStab F D.δ O _ (Vac D.δ ⊓ Fix D.δ Λ) (Vac D.δ ⊓ Fix D.δ Λ) inf_le_left (fun χ hχ => ⟨vacL F E D W _ ?_ χ hχ.1, lFix F E D W _ Λ χ hχ.2⟩)
      (lX F E D W O _) m φ (hm φ rfl)
    rw [pInf_infGL]; exact k.2
  · obtain ⟨s, hs, h1, h2⟩ := omFinite F E D W φ C hC
    have orth : ∀ g : G1 F, InfOne g → InfOrth g := by
      intro g hg i j
      have e : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
      have hg' : ∀ i j, (g.1 i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 := hg
      rw [Matrix.mul_apply, Fin.sum_univ_two, e, Matrix.transpose_apply, Matrix.transpose_apply, hg', hg', hg', hg', ← e]
      refine congrArg (fun x : A F => x.1) ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    obtain ⟨Λ, m, hm⟩ := fockEx F E D O ((fun g => W.Om g φ) '' s) (hs.image _) (by
      rintro _ ⟨g, hg, rfl⟩
      exact one _ (vacOm F E D W g (orth g (h1 g hg))) (omX F E D W O g) φ hφ)
    refine ⟨_, (fkLe F D.δ O).2 _ inf_le_left m, (fkBasic F O).2.2 _ (vacFd F E D Λ) m, fun k hk => ?_⟩
    obtain ⟨g, hg, k', a1, a2, a3⟩ := h2 k hk
    rw [a3]
    exact fkStab F D.δ O _ (Vac D.δ ⊓ Fix D.δ Λ) (Vac D.δ ⊓ Fix D.δ Λ) inf_le_left (fun χ hχ => ⟨vacOm F E D W k' (a2 (hO k hk)) χ hχ.1, omFix F E D W k' a1 Λ χ hχ.2⟩)
      (omX F E D W O k') m _ (hm _ ⟨g, hg, rfl⟩)
end
end
