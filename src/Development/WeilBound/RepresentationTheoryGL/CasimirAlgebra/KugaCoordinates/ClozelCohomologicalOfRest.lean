module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinMapEq
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.DeterminantDerivative.BigRep
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.GelfandValueOne.CasVal
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.MatrixConjugateSums.Summand
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.CoordConjAtEmb
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.TensForm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryTwistCoordinates.UnitTw

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Harmonic

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.GKHarmonic

theorem harmonic : PositivityTheory.Rg.Cz.Harmonic := by
  intro E _ _ a M _ _ _ _ κ L hd q ω hc h0
  cases q with
  | zero => exact Or.inl ⟨ω, hc, hd 0 ω hc, h0⟩
  | succ q => exact Or.inr ⟨q, ω, hc, hd _ ω hc, fun η hη h => h0 (h.symm.trans (hd q η hη))⟩

end GlobalTheory.CompanionTheory.GKHarmonic
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.EmbeddingConjugation.CoordConjEmbedding

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

section
variable {E : Type} [Field E] [NumberField E]


omit [NumberField E] in
theorem atEmb_embedding (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = (Pi.single w z : Cinf E) := by
  unfold atEmb; split_ifs <;> simp_all


omit [NumberField E] in
theorem coord_embedding (w : InfinitePlace E) (c : Cinf E) : coord w.embedding c = c w := by
  unfold coord; split_ifs <;> simp_all

theorem coord_conj_embedding [_root_.NumberField.IsTotallyComplex E] (w : InfinitePlace E) (c : Cinf E) :
    coord (ComplexEmbedding.conjugate w.embedding) c = starRingEnd ℂ (c w) := by
  set τ := ComplexEmbedding.conjugate w.embedding
  have hs : ∀ z : ℂ, (Pi.single w z : Cinf E) = atEmb τ (starRingEnd ℂ z) := by
    intro z; rw [atEmb_conj, Complex.conj_conj, atEmb_embedding]
  have h1 : coord τ (Pi.single w 1) = 1 := by rw [hs, map_one, coord_atEmb]
  have h0 : ∀ v, v ≠ w → ∀ z : ℂ, coord τ (Pi.single v z) = 0 := by
    intro v hv z
    have e0 : (Pi.single w 1 : Cinf E) * Pi.single v z = 0 := by
      funext u; by_cases hu : u = w
      · subst hu; simp [Pi.single_eq_of_ne' hv]
      · simp [Pi.single_eq_of_ne hu]
    have := congrArg (coord τ) e0
    rw [map_mul, h1, one_mul, map_zero] at this
    exact this
  have hc : c = ∑ v, (Pi.single v (c v) : Cinf E) := (Finset.univ_sum_single c).symm
  conv_lhs => rw [hc]

  rw [map_sum, Finset.sum_eq_single w (fun v _ hv => h0 v hv _) (by simp), hs, coord_atEmb]

theorem sum_emb [_root_.NumberField.IsTotallyComplex E] {R : Type*} [AddCommMonoid R] (f : (E →+* ℂ) → R) :
    ∑ τ, f τ = ∑ w : InfinitePlace E, (f w.embedding + f (ComplexEmbedding.conjugate w.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    exact (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      subst h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h) <;> subst h <;> simp [InfinitePlace.mk_conjugate_eq]
  rw [hf, Finset.sum_pair hne]

end

theorem cxExpand_holds : CxExpand := by
  intro E _ _ _ a N _ _ _ _ φ X
  let Φ : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N :=
    { toFun := fun A => φ (toL A)
      map_add' := fun A B => φ.map_add (toL A) (toL B)
      map_smul' := fun r A => φ.map_smul r (toL A) }
  let ψ : Fin a → Fin a → Cinf E →ₗ[ℝ] N := fun i j => Φ ∘ₗ (Matrix.singleLinearMap ℝ i j)
  have hψ : ∀ i j z, ψ i j z = φ (toL (Matrix.single i j z)) := fun _ _ _ => rfl
  have hcx : ∀ τ i j, cx τ φ i j = (1 / 2 : ℂ) • (ψ i j (atEmb τ 1) - Complex.I • ψ i j (atEmb τ Complex.I)) :=
    fun _ _ _ => rfl
  have key : ∀ (w : InfinitePlace E) (i j : Fin a) (c : Cinf E),
      coord w.embedding c • cx w.embedding φ i j +
          coord (ComplexEmbedding.conjugate w.embedding) c • cx (ComplexEmbedding.conjugate w.embedding) φ i j =
        ψ i j (Pi.single w (c w)) := by
    intro w i j c
    have hz : (Pi.single w (c w) : Cinf E) =
        (c w).re • (Pi.single w 1 : Cinf E) + (c w).im • (Pi.single w Complex.I : Cinf E) := by
      rw [← atEmb_embedding, atEmb_eq, atEmb_embedding, atEmb_embedding]
    rw [coord_embedding, coord_conj_embedding, hcx, hcx]
    simp only [atEmb_conj, map_one, Complex.conj_I, atEmb_embedding, Pi.single_neg, map_neg]
    rw [hz, map_add (f := _), map_smul, map_smul, ← algebraMap_smul ℂ (c w).re, ← algebraMap_smul ℂ (c w).im]
    generalize ψ i j (Pi.single w 1) = P
    generalize ψ i j (Pi.single w Complex.I) = Q
    conv_lhs => rw [← Complex.re_add_im (c w)]
    simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  have hX : φ X = ∑ i, ∑ j, ψ i j (X i j) := by

    rw [show φ X = Φ (Matrix.of X) from rfl, Matrix.matrix_eq_sum_single (Matrix.of X), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    rfl
  rw [hX]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [sum_emb (fun τ => coord τ (X i j) • cx τ φ i j), Finset.sum_congr rfl fun w _ => key w i j (X i j), ← map_sum,
  Finset.univ_sum_single]

end PositivityTheory.Rg.Cz.J

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.FrameExistence.FrameHolds

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

open PositivityTheory.Rg.Cz

section
set_option linter.unusedSectionVars false
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def c0 : ℂ := (1 + Complex.I) / 2

def ip (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∑ v, ((X * Y).trace v).re

theorem fr_eq (x : InfinitePlace E × Fin a × Fin a) :
    (fr x).1 = single x.2.1 x.2.2 (Pi.single x.1 c0 : Cinf E) + single x.2.2 x.2.1 (Pi.single x.1 (star c0) : Cinf E) := by
  show frU x + star (frU x) = _
  rw [frU, Matrix.star_eq_conjTranspose, conjTranspose_single]
  congr 2
  exact (Pi.single_star (f := fun _ : InfinitePlace E => ℂ) x.1 c0).symm

theorem fr_apply (x : InfinitePlace E × Fin a × Fin a) (p q : Fin a) (w : InfinitePlace E) :
    (fr x).1 p q w = (if x = (w, p, q) then c0 else 0) + (if x = (w, q, p) then star c0 else 0) := by
  rcases x with ⟨v, i, j⟩
  rw [fr_eq]
  simp only [Matrix.add_apply, single_apply, Pi.add_apply, Prod.mk.injEq, ite_apply, Pi.single_apply, Pi.zero_apply]
  by_cases hv : v = w
  · subst hv
    by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : j = p <;> by_cases h4 : i = q <;>
      simp [h1, h2, h3, h4]
    all_goals by_cases hc : p = q
    all_goals first | simp [hc] | simp [hc, Ne.symm hc]
  · have hv' : ¬ w = v := fun h => hv h.symm
    simp [hv, hv']

theorem ip_fr (X : Matrix (Fin a) (Fin a) (Cinf E)) (x : InfinitePlace E × Fin a × Fin a) :
    ip X (fr x).1 = (X x.2.2 x.2.1 x.1 * c0).re + (X x.2.1 x.2.2 x.1 * star c0).re := by
  rw [ip, fr_eq, Matrix.mul_add, trace_add, trace_mul_single, trace_mul_single]
  simp only [op_smul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.single_apply, mul_ite, mul_zero, Complex.add_re,
    Finset.sum_add_distrib]
  rw [Fintype.sum_eq_single x.1 (fun w hw => by simp [hw]), Fintype.sum_eq_single x.1 (fun w hw => by simp [hw])]
  simp

theorem expand (X : Matrix (Fin a) (Fin a) (Cinf E)) (hX : Xᴴ = X) :
    ∑ x, ip X (fr x).1 • (fr x).1 = X := by
  ext p q w
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, Pi.smul_apply, fr_apply, smul_add, smul_ite,
    smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ip_fr]
  have h : X q p w = star (X p q w) := by
    have h0 := congrFun (congrFun hX q) p
    rw [← h0]; rfl
  rw [h]
  generalize X p q w = z
  apply Complex.ext <;> simp [c0, Complex.real_smul] <;> ring

theorem span_fr : Submodule.span ℝ (Set.range (fr : _ → Herm E a)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨X, hX⟩ -
  have hX' : Xᴴ = X := hX
  have : (⟨X, hX⟩ : Herm E a) = ∑ x, ip X (fr x).1 • fr x := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact (expand X hX').symm
  rw [this]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

theorem iM_conjT (X : Matrix (Fin a) (Fin a) (Cinf E)) : (iM X)ᴴ = -iM Xᴴ := by
  ext p q w
  simp [iM, conjTranspose_apply]

theorem iM_neg (X : Matrix (Fin a) (Fin a) (Cinf E)) : iM (-X) = -iM X := smul_neg _ _

theorem iM_iM (X : Matrix (Fin a) (Fin a) (Cinf E)) : iM (iM X) = -X := by
  ext p q w
  simp [iM, ← mul_assoc]

theorem iM_sum {ι : Type} [Fintype ι] (r : ι → ℝ) (M : ι → Matrix (Fin a) (Fin a) (Cinf E)) :
    iM (∑ k, r k • M k) = ∑ k, r k • iM (M k) := by
  simp only [iM, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

theorem ip_neg (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : ip (-X) Y = -ip X Y := by
  simp [ip, Finset.sum_neg_distrib]

theorem fr_herm (x : InfinitePlace E × Fin a × Fin a) : (fr x).1ᴴ = (fr x).1 := (fr x).2

def cst (i j k : InfinitePlace E × Fin a × Fin a) : ℝ :=
  ip (-iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1)) (fr k).1

theorem cst_anti (i j k : InfinitePlace E × Fin a × Fin a) : cst j i k = -cst i j k := by
  rw [cst, cst, ← neg_sub, iM_neg, neg_neg, ← ip_neg, neg_neg]

theorem cst_comm (i j : InfinitePlace E × Fin a × Fin a) :
    (fr i).1 * (fr j).1 - (fr j).1 * (fr i).1 = ∑ k, cst i j k • iM (fr k).1 := by
  have hH : (-iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1))ᴴ = -iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1) := by
    rw [conjTranspose_neg, iM_conjT, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, fr_herm, fr_herm,
      ← neg_sub, iM_neg]
    simp only [neg_neg]
  rw [← iM_sum]
  simp only [cst]
  rw [expand _ hH, iM_neg, iM_iM, neg_neg]

theorem cst_third (k j : InfinitePlace E × Fin a × Fin a) :
    iM (fr k).1 * (fr j).1 - (fr j).1 * iM (fr k).1 = ∑ i, cst i j k • (fr i).1 := by
  set Z := (fr k).1
  set Y := (fr j).1
  have hL : (iM Z * Y - Y * iM Z)ᴴ = iM Z * Y - Y * iM Z := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, iM_conjT, fr_herm, fr_herm]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel
  have key : ∀ i, cst i j k = ip (iM Z * Y - Y * iM Z) (fr i).1 := by
    intro i
    set F := (fr i).1
    have ht : ((iM Z * Y - Y * iM Z) * F).trace = -(iM (F * Y - Y * F) * Z).trace := by
      simp only [iM, Matrix.smul_mul, Matrix.mul_smul, sub_mul, trace_sub, trace_smul]
      rw [← trace_mul_cycle Y F Z, trace_mul_cycle Y Z F]
      simp only [smul_eq_mul]
      ring
    rw [cst, ip_neg, ip, ip, ht]
    simp [Finset.sum_neg_distrib]
    rfl
  simp_rw [key]
  exact (expand _ hL).symm

end

theorem frame_holds : Frame := by
  intro E _ _ a
  exact ⟨span_fr, cst, cst_anti, cst_comm, cst_third⟩

end PositivityTheory.Rg.Cz.J
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomologicalOfRest

section

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_rest (h1 : KType) (hgk : GKData) (hw : WhitLie) (hka : KugaAbs) (hkg : KugaGlue)
    (hcg : CoefGlue) (hco : Cochain) (hcb : CasBound) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of h1 J.kData_holds hgk hw GlobalTheory.CompanionTheory.RgCz.charInt J.unitTw_holds
    (hcg hcb J.bigRep_holds J.bigCx_holds J.summand_holds hco J.casVal_holds)
    (hkg hka J.frame_holds GlobalTheory.CompanionTheory.FrameCasimir.frameCas J.cxExpand_holds J.tensForm_holds GlobalTheory.CompanionTheory.GKHarmonic.harmonic)

end PositivityTheory.Rg.Cz
end
end
