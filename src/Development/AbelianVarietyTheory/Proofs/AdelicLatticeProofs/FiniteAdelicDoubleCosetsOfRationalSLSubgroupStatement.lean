module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducibleStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpanStatement
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImage
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPartStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosureStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroupStatement
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSpanBlockDiagPartImageLt

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finrank_span_blk_image_lt :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  intro ι _ _ Γ e a ha ha0 hblk

  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun x => blk e x
      map_add' := fun x y => by
        simp only [blk, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c x => by
        simp only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L := by
    rw [Submodule.map_span]
    rfl
  rw [himg]

  set S := Submodule.span ℂ Γ with hS
  let f := L.domRestrict S
  have hrange : LinearMap.range f = S.map L := LinearMap.range_domRestrict S L
  have hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]
    exact hblk
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    exact ha0 (congrArg Subtype.val hker)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  omega

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSpanBlockDiagPartImageLtStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.finrank_span_blockDiagPart_image_lt : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  first | exact @GlobalTheory.ClassFin.finrank_span_blk_image_lt | exact GlobalTheory.ClassFin.finrank_span_blk_image_lt | (intros; apply GlobalTheory.ClassFin.finrank_span_blk_image_lt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImageStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → AdelicPair R R₀ → CF (blk e '' Γ) R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_cf_blk_image | exact GlobalTheory.ClassFin.cf_of_cf_blk_image | (intros; apply GlobalTheory.ClassFin.cf_of_cf_blk_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroup

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem subset_pts (Γ : Set (Matrix ι ι ℂ)) : Γ ⊆ pts Γ ℂ := fun g hg _ hf => hf g hg

omit [Fintype ι] [DecidableEq ι] in
theorem vanI_pts (Γ : Set (Matrix ι ι ℂ)) : vanI (pts Γ ℂ) = vanI Γ := by
  ext f
  exact ⟨fun h g hg => h g (subset_pts Γ hg), fun h g hg => hg f h⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ev_map_aut (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Matrix.map_apply]

theorem exists_poly_of_dual (φ : Module.Dual ℂ (Matrix ι ι ℂ)) :
    ∃ f : MvPolynomial (ι × ι) ℂ, ∀ g, evC f g = φ g := by
  refine ⟨∑ ij : ι × ι, MvPolynomial.C (φ (Matrix.single ij.1 ij.2 1)) * MvPolynomial.X ij, fun g => ?_⟩
  conv_rhs => rw [Matrix.matrix_eq_sum_single g]

  simp only [evC, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (g i j) = g i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem ratClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  intro ι _ _ Γ h
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ h ℂ
  refine ⟨⟨⟨h1, h2, h3, h4, ?_⟩, ?_⟩, vanI_pts Γ, ?_⟩
  · intro σ g hg f hf
    rw [ev_map_aut, hg f hf, map_zero]
  · intro g hg f hf
    exact hg f (by rw [vanI_pts]; exact hf)
  · refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono (subset_pts Γ))
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (Submodule.span ℂ Γ) y).1 fun φ hφ => ?_
    obtain ⟨f, hf⟩ := exists_poly_of_dual φ
    rw [← hf]
    refine GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι Γ h.aut_mem f (fun g hg => ?_) y hy
    rw [hf]
    exact (Submodule.mem_dualAnnihilator φ).1 hφ g (Submodule.subset_span hg)

end GlobalTheory.ClassFin.RatClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroupStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  first | exact @GlobalTheory.ClassFin.RatClosure.ratClosure | exact GlobalTheory.ClassFin.RatClosure.ratClosure | (intros; apply GlobalTheory.ClassFin.RatClosure.ratClosure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact GlobalTheory.T.classFiniteness_completelyReducible ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group ι (blk e '' Γ) hPre
      have hlt := GlobalTheory.T.finrank_span_blockDiagPart_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroupStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_isQGroup | exact GlobalTheory.ClassFin.cf_of_isQGroup | (intros; apply GlobalTheory.ClassFin.cf_of_isQGroup <;> assumption)
end
end
