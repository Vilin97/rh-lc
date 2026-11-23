module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
import Formalism.LocalToGlobal.HermitianForms.Interlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrOneGFull
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapMemCSpanOfRat
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormOneOfPow
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.RestrictionSymmetric

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllBrTenLe

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

def BlockFockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ) (c : ι → ℝ),
    (∀ τ, ∀ f ∈ V τ, (Formalism.REAL.fockF (F τ f) (F τ f)).re ≤ c τ ^ 2 * (Formalism.REAL.fockF f f).re) →
    ∀ P ∈ Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f},
      (Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P)).re ≤
        (∏ τ, c τ ^ 2) * (Formalism.REAL.fockF P P).re

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def eX {k : ℕ} (l : DomWeight k) : ℝ := (Formalism.REAL.fockF (extremal ℂ k l) (extremal ℂ k l)).re

theorem eX_pos {k : ℕ} (l : DomWeight k) : 0 < eX l := by
  have h := (Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.L2.Ker.lm_extremal_ne (K := ℂ) l)).1
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.ofReal_re] at h
  exact h

theorem normFock_re {k : ℕ} (l : DomWeight k) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    (normFock l f f).re = (Formalism.REAL.fockF f f).re / eX l := by
  unfold normFock eX
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.div_ofReal_re, Complex.ofReal_re]

def cF (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.fm u).beOn τ * Real.sqrt (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ))

theorem cF_sq (τ : D.what₂.Tau) :
    cF D u τ ^ 2 = (D.fm u).beOn τ ^ 2 * (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ)) := by
  unfold cF
  rw [mul_pow, Real.sq_sqrt (div_nonneg (eX_pos _).le (eX_pos _).le)]

theorem factor_le (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hf : f ∈ delSq ℂ _ ((D.fm u).lam D.R.m τ)) :
    (Formalism.REAL.fockF (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
      (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤ cF D u τ ^ 2 * (Formalism.REAL.fockF f f).re := by
  have hI := interlaceTr D u (sg_interlace Tf.valP) τ
  have hI' := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI
  have hf' : f ∈ nablaSq ℂ _ (lamTr D u τ) := by
    rw [Formalism.L2.Col.nablaSq_eq_delSq]; unfold lamTr; rw [delSq_wSh]; exact hf
  have h := Formalism.L2.Ker.nm_le _ _ _ hI' hS f hf'
  have hb : (D.fm u).beOn τ ^ 2 = ((Formalism.L2.Col.Br.cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 *
      Formalism.L2.Col.Br.kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
    rw [beOn_closedS Tf hB τ]
    unfold Formalism.L2.Ker.beOnVal
    rw [mul_pow, sq_abs, Real.sq_sqrt (Formalism.L2.Ker.nm_kapR_pos _ _ _ hI' hS).le]
  have eS : eX (sgTr D u τ) = eX ((D.fm u).sg τ) := by unfold eX sgTr; rw [extremal_wSh]
  have eL : eX (lamTr D u τ) = eX ((D.fm u).lam D.R.m τ) := by unfold eX lamTr; rw [extremal_wSh]
  rw [normFock_re, normFock_re, eS, eL, ← hb] at h
  have hs := eX_pos ((D.fm u).sg τ)
  have hl := eX_pos ((D.fm u).lam D.R.m τ)
  rw [div_le_iff₀ hs] at h
  rw [cF_sq]
  calc _ ≤ (D.fm u).beOn τ ^ 2 * ((Formalism.REAL.fockF f f).re / eX ((D.fm u).lam D.R.m τ)) * eX ((D.fm u).sg τ) := h
    _ = _ := by field_simp

theorem nfAll_brTen_le (hT : BlockFockBound) (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re := by
  have key := hT D.what₂.Tau (D.R.N D.R.m) (D.R.N D.R.m - 1) (fun τ => delSq ℂ _ ((D.fm u).lam D.R.m τ))
    (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (cF D u)
    (fun τ f hf => factor_le Tf hB τ f hf) P hP
  have eprod : ∀ {k : ℕ} (l : D.what₂.Tau → DomWeight k),
      ∏ τ, Formalism.REAL.fockF (extremal ℂ k (l τ)) (extremal ℂ k (l τ)) = ((∏ τ, eX (l τ) : ℝ) : ℂ) := by
    intro k l
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.nm_fockF_self _
  unfold Formalism.L2.Forms.nfAll
  rw [eprod, eprod, Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hs : 0 < ∏ τ, eX ((D.fm u).sg τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hl : 0 < ∏ τ, eX ((D.fm u).lam D.R.m τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hc : ∏ τ, cF D u τ ^ 2 =
      (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => cF_sq τ
  rw [hc] at key
  rw [div_le_iff₀ hs]
  calc (Formalism.REAL.fockF (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re
      ≤ (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) *
          (Formalism.REAL.fockF P P).re := key
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.BlkFockLe

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Matrix
open scoped ComplexOrder

section Fock

variable {σ : Type}

theorem tf_eq_sum (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [notMem_support_iff.mp hm]
  simp

theorem tf_add_left (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [tf_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
    tf_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tf_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem tf_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [tf_eq_sum (c • f) g f.support support_smul, tf_eq_sum f g f.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem tf_add_right (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem tf_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

def tfB : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) Formalism.REAL.fockF tf_add_left tf_smul_left tf_add_right tf_smul_right

theorem tfB_apply (f g : MvPolynomial σ ℂ) : tfB f g = Formalism.REAL.fockF f g := rfl

theorem tf_eq_fockS (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockS g f := by
  classical
  rw [tf_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  ring

theorem tf_star (f g : MvPolynomial σ ℂ) : star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [tf_eq_fockS g f]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  simp only [star_mul', star_star, star_natCast]

theorem tf_quad {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (x : Fin k → ℂ) :
    star x ⬝ᵥ (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) *ᵥ x =
      Formalism.REAL.fockF (∑ j, x j • w j) (∑ i, x i • w i) := by
  rw [← tfB_apply]

  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, tfB_apply, smul_eq_mul,
  dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem tf_herm {σ' : Type} {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (v : Fin k → MvPolynomial σ' ℂ) (r : ℝ) :
    (((r : ℂ) • Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) - Matrix.of fun i j => Formalism.REAL.fockF (v j) (v i)).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, star_sub, star_mul',
    tf_star]
  rw [Complex.star_def, Complex.conj_ofReal]

theorem tf_gram_psd {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) :
    (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp only [conjTranspose_apply, Matrix.of_apply, tf_star]
  · rw [tf_quad, Formalism.L2.Ker.nm_fockF_self]
    exact Complex.zero_le_real.2 (Formalism.L2.Ker.nm_fockF_nonneg _)

end Fock

section Had

variable {ι : Type} [Fintype ι] {k : ℕ}

theorem tf_ones_psd : (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp
  · have : star x ⬝ᵥ (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, mulVec, Matrix.of_apply, one_mul, star_sum, Finset.sum_mul, Pi.star_apply]
    rw [this]
    exact star_mul_self_nonneg _

theorem tf_had_sub (A B : ι → Matrix (Fin k) (Fin k) ℂ) (hB : ∀ τ, (B τ).PosSemidef) (hAB : ∀ τ, (A τ - B τ).PosSemidef) :
    ((Matrix.of fun i j => ∏ τ, A τ i j) - Matrix.of fun i j => ∏ τ, B τ i j).PosSemidef := by
  classical
  have hA : ∀ τ, (A τ).PosSemidef := fun τ => by simpa using (hAB τ).add (hB τ)
  suffices h : ∀ s : Finset ι, ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      (Matrix.of fun i j => ∏ τ ∈ s, A τ i j).PosSemidef from (h Finset.univ).1
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact ⟨PosSemidef.zero, tf_ones_psd⟩
  | insert t s ht ih =>
    have eA : (Matrix.of fun i j => ∏ τ ∈ insert t s, A τ i j) = A t ⊙ Matrix.of fun i j => ∏ τ ∈ s, A τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have eB : (Matrix.of fun i j => ∏ τ ∈ insert t s, B τ i j) = B t ⊙ Matrix.of fun i j => ∏ τ ∈ s, B τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have e : A t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - B t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, B τ i j) =
        (A t - B t) ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) +
          B t ⊙ ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j) := by
      ext i j; simp [hadamard]; ring
    refine ⟨?_, ?_⟩
    · rw [eA, eB, e]
      exact ((hAB t).hadamard ih.2).add ((hB t).hadamard ih.1)
    · rw [eA]; exact (hA t).hadamard ih.2

end Had

theorem tf_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.ten f) (Formalism.MainNotions.product_first_zeroth_parts.ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [tf_eq_fockS]
  have h := Formalism.L2.DIV.fockSymTensor_holds ℂ ι n g f
  refine (h.trans ?_)
  exact Finset.prod_congr rfl fun τ _ => (tf_eq_fockS _ _).symm

theorem blkFockLe : BlockFockBound := by
  intro ι _ n n' V F c hF P hP
  classical
  obtain ⟨k, a, p, hsum⟩ := Submodule.mem_span_set'.1 hP
  choose f hfV hfeq using fun i => (p i).2
  have hs : ∀ (r : ℂ) (M : Matrix (Fin k) (Fin k) ℂ) (v : Fin k → ℂ), (r • M) *ᵥ v = r • (M *ᵥ v) := by
    intro r M v; ext i
    simp only [mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hd : ∀ (r : ℂ) (v w : Fin k → ℂ), v ⬝ᵥ (r • w) = r * (v ⬝ᵥ w) := by
    intro r v w
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP' : P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (f i) := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ => by rw [hfeq i]
  have hblk : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ)) := by

    rw [hP', map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Formalism.MainNotions.product_first_zeroth_parts.blk_ten]
  set G : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (f j τ) (f i τ) with hG
  set H : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (F τ (f j τ)) (F τ (f i τ)) with hH
  have qP : Formalism.REAL.fockF P P = star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, G τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (f i)) a
    simp only [tf_ten] at this
    rw [hP', ← this]
    rfl
  have qB : Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) =
      star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, H τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ))) a
    simp only [tf_ten] at this
    rw [hblk, ← this]
    rfl
  have hBpsd : ∀ τ, (H τ).PosSemidef := fun τ => tf_gram_psd (fun i => F τ (f i τ))
  have hABpsd : ∀ τ, ((((c τ ^ 2 : ℝ) : ℂ) • G τ) - H τ).PosSemidef := by
    intro τ
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨tf_herm (fun i => f i τ) (fun i => F τ (f i τ)) (c τ ^ 2), fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, hs, hd, tf_quad, tf_quad]
    have hlin : ∑ i, x i • F τ (f i τ) = F τ (∑ i, x i • f i τ) := by rw [map_sum]; simp [map_smul]
    have hmem : ∑ i, x i • f i τ ∈ V τ := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfV i τ)
    rw [hlin, Formalism.L2.Ker.nm_fockF_self (∑ i, x i • f i τ), Formalism.L2.Ker.nm_fockF_self (F τ (∑ i, x i • f i τ)),
      ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (sub_nonneg.2 (hF τ _ hmem))
  have key := (tf_had_sub (fun τ => ((c τ ^ 2 : ℝ) : ℂ) • G τ) H hBpsd hABpsd).dotProduct_mulVec_nonneg a
  have eA : (Matrix.of fun i j => ∏ τ, (((c τ ^ 2 : ℝ) : ℂ) • G τ) i j) =
      (((∏ τ, c τ ^ 2 : ℝ) : ℂ)) • Matrix.of fun i j => ∏ τ, G τ i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [eA, sub_mulVec, dotProduct_sub, hs, hd, ← qP, ← qB,
    Formalism.L2.Ker.nm_fockF_self P, Formalism.L2.Ker.nm_fockF_self (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P), ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.zero_le_real] at key
  exact sub_nonneg.1 key

theorem nfAll_brTen_le' {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re :=
  nfAll_brTen_le blkFockLe Tf hB P hP

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormalFormAgree

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Gen

theorem norm_detPow_sq {n : ℕ} (g : GL (Fin n) ℂ) (e : ℤ) :
    ‖detPow ℂ n g e‖ ^ 2 = ‖(g : Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * e) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm e]
  norm_num

theorem desc_scalar {K σ : Type} [Field K] (j : K →+* ℂ) (Q F : MvPolynomial σ K) (χ : ℂ) (k : ℕ) (hk : 0 < k)
    (hχ : χ ^ k = 1) (h : map j Q = χ⁻¹ • map j F) : ∃ a : K, Q = a • F ∧ ∀ s : K →+* ℂ, ‖s a‖ ≤ 1 := by
  have hinj : Function.Injective (map (σ := σ) j) := MvPolynomial.map_injective _ j.injective
  by_cases hF : F = 0
  · refine ⟨0, ?_, fun s => by simp⟩
    apply hinj
    rw [h, hF]
    simp
  · obtain ⟨m, hm⟩ : ∃ m, F.coeff m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hF (MvPolynomial.ext _ _ fun m => by simp [hc m])
    have hc : j (Q.coeff m) = χ⁻¹ * j (F.coeff m) := by
      have := congrArg (AddMonoidAlgebra.coeff · m) h
      rwa [coeff_map, MvPolynomial.coeff_smul, coeff_map, smul_eq_mul] at this
    have hjm : j (F.coeff m) ≠ 0 := (map_ne_zero j).2 hm
    have ha : j (Q.coeff m / F.coeff m) = χ⁻¹ := by
      rw [map_div₀, hc, mul_div_assoc, div_self hjm, mul_one]
    refine ⟨Q.coeff m / F.coeff m, ?_, fun s => ?_⟩
    · apply hinj
      rw [h, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul F (Q.coeff m / F.coeff m), map_mul, map_C, ha]
    · have := norm_one_of_pow j s _ k hk (by rw [ha, inv_pow, hχ, inv_one])
      rw [this]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem normal_form_agree {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.nfAll lam p p = Formalism.L2.Forms.nfAll lam p p := rfl

theorem norm_sqrtT_sq (d : ℤ) : ‖(((sqrtT D u) ^ d : ℂˣ) : ℂ)‖ ^ 2 = ((D.mem u).A.T : ℝ) ^ d := by
  have hT : (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) := Nat.cast_nonneg _
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  have h1 : ‖((sqrtT D u : ℂˣ) : ℂ)‖ = Real.sqrt ((D.mem u).A.T : ℝ) := by
    simp only [sqrtT, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, ← zpow_natCast, ← _root_.zpow_mul, mul_comm d, _root_.zpow_mul, zpow_natCast, Real.sq_sqrt hT]

theorem chain_at (Tf : FormsTiedSym D u Ch chOf) (hBe : Formalism.L2.Ker.BeOnTie D u)
    (o' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho' : ∀ τ, IsUnit (o' τ).det)
    (Y : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hY : Y ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re ≤
      ptB D u * ((∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y)
          (blkRow (fun τ => dOT u (o' τ)) Y)).re) := by
  classical
  have hT : ∀ τ, IsUnit ((o' τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact ho' τ
  let g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ := fun τ =>
    ⟨(o' τ)ᵀ, ((o' τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have hg : ∀ τ, ((g τ : GL _ ℂ) : Matrix _ _ ℂ) = (o' τ)ᵀ := fun τ => rfl
  have hL1 : blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Y =
      (∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift) • blkRow (fun τ => dOT u (o' τ)) Y := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((gFull D u (g τ) : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = fun τ => dOT u (o' τ) :=
      funext fun τ => transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ)
    rw [e]
  have hR1 : blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Y) =
      (∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift) • subP o' (Formalism.L2.Ker.brTen D u Y) := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((g τ : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = o' := funext fun τ => by rw [hg, Matrix.transpose_transpose]
    rw [e]
    rfl
  have key := brTen_blk_gFull Tf g Y
  rw [hL1, hR1, map_smul, smul_smul] at key
  have hn := congrArg (fun p => (Formalism.L2.Forms.nfAll (D.fm u).sg p p).re) key
  simp only [nfAll_smul_reB, normal_form_agree] at hn
  have hdO : ∀ τ, IsUnit (dOT u (o' τ)).det := fun τ => by
    rw [det_dOT]
    exact (ho' τ).mul (Units.isUnit _)
  have hZ := blkRow_mem_CSpan ((D.fm u).lam D.R.m) (fun τ => dOT u (o' τ)) hdO Y hY
  have hle := nfAll_brTen_le' Tf hBe _ hZ

  have hshL : ∀ τ, (lamTr D u τ).detShift = shiftOf (lamT u D.R.m) τ := fun τ => by rw [shift_lamTr]
  have hshS : ∀ τ, (sgTr D u τ).detShift = shiftOf (sgT u) τ := fun τ => by
    have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
    have hS : (sgTr D u τ).detShift = (lamTr D u τ).detShift := Formalism.L2.Ker.sameShiftTr D u τ hI0
    rw [hS, hshL, shift_lamT_sgTS Tf τ]
  have hk1 : ‖∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift‖ ^ 2 =
      ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshL, ← transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ), Matrix.det_transpose]
  have hk2 : ‖∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift‖ ^ 2 = ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshS, hg, Matrix.det_transpose]
  have hcT : ‖∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)‖ ^ 2 = ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun τ _ => norm_sqrtT_sq _
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hcpos : 0 < ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := Finset.prod_pos fun τ _ => zpow_pos hTpos _
  have hptB : ptB D u * ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) = ∏ τ, (D.fm u).beOn τ ^ 2 := by
    unfold ptB
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg]
    field_simp
  rw [norm_mul, mul_pow, hk1, hk2, hcT] at hn
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re
  set nBZ := (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))
    (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))).re
  set nZ := (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y) (blkRow (fun τ => dOT u (o' τ)) Y)).re
  set K1 := ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  set K2 := ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set CT := ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ)
  set B := ∏ τ, (D.fm u).beOn τ ^ 2
  have hK1 : 0 ≤ K1 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  calc K2 * nW = (CT * K2 * nW) / CT := by field_simp
    _ = K1 * nBZ / CT := by rw [← hn]
    _ ≤ K1 * (B * nZ) / CT := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK1) hcpos.le
    _ = ptB D u * (K1 * nZ) := by rw [← hptB]; field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end
