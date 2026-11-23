module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEqStatement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEqStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGL

section

@[expose] public section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbIsLat

theorem single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem stdLat_eq_span {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    stdLat O n = Submodule.span O (Set.range fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLat] at hv
    choose a ha using hv
    have hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLat n i

theorem stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.LatOrbIsLat

open GlobalTheory.LatOrbIsLat in
theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by

    simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGLStatement

section

@[expose] public section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.isFullRankLattice_image_standardLattice_GL : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.matLat_stdLat_isLatV | exact GlobalTheory.LatOrb.matLat_stdLat_isLatV | (intros; apply GlobalTheory.LatOrb.matLat_stdLat_isLatV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitary

section

@[expose] public section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by

  simp only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
  Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem selfDual_matLat_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this

end GlobalTheory.LatOrb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitaryStatement

section

@[expose] public section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.isSelfDual_image_standardLattice_unitary : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.selfDual_matLat_stdLat | exact GlobalTheory.LatOrb.selfDual_matLat_stdLat | (intros; apply GlobalTheory.LatOrb.selfDual_matLat_stdLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCoset

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.OrbitT

open GlobalTheory.LatOrb

theorem stable_of_conj {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (g : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K)
    (h : matLat O ((g⁻¹ : GL (Fin n) K).val * γ * g.val) (stdLat O n) = stdLat O n) :
    ∀ v ∈ matLat O g.val (stdLat O n), γ *ᵥ v ∈ matLat O g.val (stdLat O n) := by
  intro v hv
  have e : γ * g.val = g.val * ((g⁻¹ : GL (Fin n) K).val * γ * g.val) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : matLat O γ (matLat O g.val (stdLat O n)) = matLat O g.val (stdLat O n) := by
    rw [← matLat_mul, e, matLat_mul, h]
  rw [← h2]
  exact (mem_matLat _ _ _).2 ⟨v, hv, rfl⟩

theorem orbit_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  intro E _ _ _ n w hcc hcv P₀ hcop γ hγ g₁ g₂ h₁ h₂
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  have hσO : ∀ a : w.adicCompletionIntegers E, ∃ b : w.adicCompletionIntegers E,
      cj w (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a) =
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) b := by
    intro a
    refine ⟨⟨cj w a, ?_⟩, rfl⟩
    have ha := a.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hcv]; exact ha
  have hK : ∀ h : UL n w, h ∈ KL n w ↔ matLat (w.adicCompletionIntegers E) h.1.val
      (stdLat (w.adicCompletionIntegers E) n) = stdLat (w.adicCompletionIntegers E) n := by
    intro h
    exact (Subgroup.mem_subgroupOf).trans (GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq (w.adicCompletionIntegers E) n h.1)
  have st : ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w → ∀ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n), γ.1.val *ᵥ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n) := by
    intro g hg
    have h := (hK _).1 hg
    have e : ((g⁻¹ * γ * g : UL n w).1.val) = (g.1⁻¹ : GLw n w).val * γ.1.val * g.1.val := by simp
    rw [e] at h
    exact stable_of_conj g.1 γ.1.val h
  obtain ⟨t, htU, htc, htM⟩ : ∃ t : GLw n w, t ∈ UL n w ∧ t * γ.1 = γ.1 * t ∧
      matLat (w.adicCompletionIntegers E) t.val (matLat (w.adicCompletionIntegers E) g₁.1.val
        (stdLat (w.adicCompletionIntegers E) n)) = matLat (w.adicCompletionIntegers E) g₂.1.val
        (stdLat (w.adicCompletionIntegers E) n) := by
    obtain ⟨p, hpu, hp⟩ := GlobalTheory.T.exists_unit_eq_of_stable_lattices n P₀ hcop γ.1.val hγ _ _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1) (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₂.1) (st g₁ h₁) (st g₂ h₂)
    by_cases hs : IsSplitAt w
    · refine ⟨hpu.unit, by simp [UL, hs], ?_, hp.symm⟩
      ext : 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      have e1 : aeval γ.1.val p * γ.1.val = aeval γ.1.val (p * X) := by rw [map_mul, aeval_X]
      have e2 : γ.1.val * aeval γ.1.val p = aeval γ.1.val (X * p) := by rw [map_mul, aeval_X]
      rw [e1, e2, mul_comm]
    · have hUL : ∀ h : UL n w, ((h.1.val).map (cj w))ᵀ * h.1.val = 1 := by
        intro h
        have := h.2
        simp only [UL, hs, if_false] at this
        simpa [UJ, cT] using this
      have sd : ∀ g : UL n w, SelfDual (w.adicCompletionIntegers E) (cj w)
          (matLat (w.adicCompletionIntegers E) g.1.val (stdLat (w.adicCompletionIntegers E) n)) :=
        fun g => GlobalTheory.T.isSelfDual_image_standardLattice_unitary (cj w) hcc hσO n _ (hUL g)
      have hc := GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices (cj w) hcc n (aeval γ.1.val p) hpu _ (sd g₁) (hp ▸ sd g₂)
      obtain ⟨t, ht1, htc, htM⟩ := GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq n P₀ hcop γ.1.val hγ (cj w) hcc hσO (hUL γ) _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1)
        (st g₁ h₁) p hpu hc
      have htu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse ht1)
      refine ⟨htu.unit, ?_, ?_, by rw [hp]; exact htM⟩
      · show _ ∈ UL n w
        simp only [UL, hs, if_false]
        show cT (cj w) _ * 1 * _ = 1
        simpa [cT] using ht1
      · ext : 1
        simpa using htc
  refine ⟨⟨t, htU⟩, ?_, (⟨t, htU⟩ * g₁)⁻¹ * g₂, ?_, by group⟩
  · show (⟨t, htU⟩ : UL n w) * γ = γ * (⟨t, htU⟩ : UL n w)
    exact Subtype.ext htc
  · rw [hK]
    have e : (((⟨t, htU⟩ : UL n w) * g₁)⁻¹ * g₂ : UL n w).1.val =
        (g₁.1⁻¹ : GLw n w).val * ((t⁻¹ : GLw n w).val * g₂.1.val) := by simp [mul_assoc]
    rw [e, matLat_mul, matLat_mul, ← htM, ← matLat_mul (a := ((t⁻¹ : GLw n w).val)), Units.inv_mul, matLat_one,
      ← matLat_mul, Units.inv_mul, matLat_one]

end GlobalTheory.BCT.OrbitT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  exact @GlobalTheory.BCT.OrbitT.orbit_main
end
end
