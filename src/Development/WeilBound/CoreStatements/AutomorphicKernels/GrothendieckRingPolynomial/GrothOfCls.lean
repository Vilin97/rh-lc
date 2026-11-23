module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleCast
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.JacquetFunctionalClass
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.JhMultSegCl
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MultOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlattenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltSum

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace PositivityTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end PositivityTheory.Groth.AltS

namespace PositivityTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  apply CompanionTheory.Groth.altSum <;> assumption

end PositivityTheory.Groth

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleFold

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult



namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem class_of_finite_length {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : HasFiniteLength π) : cl0 π = clsGL π h := by
  rw [cl0, dite_eq_left h]

theorem class_congr_iso {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv τ) :
    cl0 π = cl0 τ := by
  by_cases h : HasFiniteLength π
  · have h' : HasFiniteLength τ := h.of_equiv φ
    rw [class_of_finite_length h, class_of_finite_length h', clsGL_congr φ h h']
  · have h' : ¬ HasFiniteLength τ := fun h' => h (h'.of_equiv φ.symm)
    rw [cl0, cl0, dite_eq_right h, dite_eq_right h']

theorem class_chosen_rep_basis (x : IrrGL (k := k)) : cl0 x.rep = sg x := by
  rw [class_of_finite_length x.2.rep.hasFiniteLength]
  exact (clsGL_irr x.2.rep _).trans (by rw [IrrCl.cl_rep]; rfl)

theorem prodIrr_cast {h h' N N' : ℕ} (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N') :
    (HasFiniteLength (prodIrr x hx) ↔ HasFiniteLength (prodIrr y hy)) ∧
      cl0 (prodIrr x hx) = cl0 (prodIrr y hy) := by
  subst e
  have hxy' : x = y := funext fun i => hxy i
  subst hxy'
  have hN : N = N' := hx.symm.trans hy
  subst hN
  exact ⟨Iff.rfl, rfl⟩

theorem prodIrr_zero {N : ℕ} (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    HasFiniteLength (prodIrr x hd) ∧ cl0 (prodIrr x hd) = GrothGL.unit k := by
  obtain rfl : N = 0 := by simpa using hd.symm
  obtain ⟨φ⟩ := GlobalTheory.LocGL.Tests.nonempty_equiv_prodIrr_zero x hd
  have h1 : HasFiniteLength (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ :=
    (IrrRep.det (Fin 0) 1 isSmoothChar_one).hasFiniteLength
  have hfl : HasFiniteLength (prodIrr x hd) := h1.of_equiv φ
  refine ⟨hfl, ?_⟩
  rw [← class_congr_iso φ]
  exact (class_of_finite_length h1).trans (clsGL_irr _ _)

theorem prodIrr_one (x : IrrGL (k := k)) (hd : ∑ _ : Fin 1, x.1 = x.1) :
    HasFiniteLength (prodIrr (fun _ : Fin 1 => x) hd) ∧ cl0 (prodIrr (fun _ : Fin 1 => x) hd) = sg x := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one x hd
  exact ⟨x.2.rep.hasFiniteLength.of_equiv φ, (class_congr_iso φ).symm.trans (class_chosen_rep_basis x)⟩

theorem class_of_product_equiv (hM : MulCls k) {r t : ℕ} {U W X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (π₁ : Representation ℂ (GL (Fin r) k) U)
    (π₂ : Representation ℂ (GL (Fin t) k) W) (τ : Representation ℂ (GL (Fin (r + t)) k) X)
    (F : (prod₂ π₁ π₂).Equiv τ) (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂) (s₁ : IsSmooth π₁)
    (s₂ : IsSmooth π₂) : HasFiniteLength τ ∧ cl0 τ = mulR (cl0 π₁) (cl0 π₂) := by
  obtain ⟨h, hc⟩ := hM r t U W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h.of_equiv F, (class_congr_iso F).symm.trans hc⟩

theorem prodIrr_append_one (hM : MulCls k) {h : ℕ} (x₀ : IrrGL (k := k)) (y : Fin h → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = ∑ a, (y a).1) (hfl : HasFiniteLength (prodIrr y hy))
    (happ : ∑ a, (Fin.append (fun _ : Fin 1 => x₀) y a).1 = x₀.1 + ∑ a, (y a).1) :
    HasFiniteLength (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) ∧
      cl0 (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) = mulR (sg x₀) (cl0 (prodIrr y hy)) := by
  have hx1 : ∑ _ : Fin 1, x₀.1 = x₀.1 := by simp
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k 1 h x₀.1 (∑ a, (y a).1) (fun _ : Fin 1 => x₀) y hx1 hy happ
  have H1 := prodIrr_one x₀ hx1
  have H3 := class_of_product_equiv hM (prodIrr (fun _ : Fin 1 => x₀) hx1) (prodIrr y hy) _ F H1.1 hfl
    (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
  exact ⟨H3.1, H3.2.trans (congrArg (fun a => mulR a (cl0 (prodIrr y hy))) H1.2)⟩

theorem class_product_irreducible_fold (hM : MulCls k) : ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
    HasFiniteLength (prodIrr x hd) ∧
      cl0 (prodIrr x hd) = (List.ofFn x).foldr (fun y a => mulR (sg y) a) (GrothGL.unit k) := by
  apply CompanionTheory.Groth.class_product_irreducible_fold <;> assumption


variable (k) in
theorem prodList (h : MulCls k) : ProdList k :=
  fun n N x hd => (class_product_irreducible_fold h n N x hd).2

end PositivityTheory.Groth

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MulClassBasisRight

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdReorder



namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckAssociativity

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : Nonempty (π.Equiv τ)) : cl0 π = cl0 τ := by
  obtain ⟨φ⟩ := φ
  unfold cl0
  by_cases h : HasFiniteLength π
  · rw [dif_pos h, dif_pos (h.of_equiv φ)]
    exact clsGL_congr φ _ _
  · rw [dite_eq_right h, dite_eq_right (fun h' => h (h'.of_equiv φ.symm))]

theorem class_induced_cast {r t N : ℕ} (h : r + t = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    cl0 (ind₂ (stdSum h) ρ) = cl0 (ind₂ (stdSum (rfl : r + t = r + t)) ρ) := by
  subst h
  rfl

theorem class_of_chosen_rep (x : IrrGL (k := k)) : cl0 (IrrGL.rep x) = sg x := by
  exact (dif_pos x.2.rep.hasFiniteLength).trans ((clsGL_irr x.2.rep x.2.rep.hasFiniteLength).trans
    (congrArg (fun c => Finsupp.single (⟨x.1, c⟩ : IrrGL (k := k)) (1 : ℤ)) x.2.cl_rep))

theorem mulR_sg (x y : IrrGL (k := k)) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) := by
  have h1 := Finsupp.sum_single_index (a := x) (b := (1 : ℤ)) (h := fun z m => (sg y).sum fun w n => (m * n) • cl0 (prod₂ (IrrGL.rep z) (IrrGL.rep w))) (by simp only [Finsupp.sum, zero_mul, zero_smul, Finset.sum_const_zero])
  have h2 := Finsupp.sum_single_index (a := y) (b := (1 : ℤ)) (h := fun w n => ((1 : ℤ) * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep w))) (by simp only [mul_zero, zero_smul])
  exact h1.trans (h2.trans (by simp only [mul_one, one_smul]))

theorem assoc_gen (h : MulCls k) {r s t : ℕ} {V₁ V₂ V₃ U U' : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂)
    (π₃ : Representation ℂ (GL (Fin t) k) V₃) (P : Representation ℂ (GL (Fin (r + s)) k) U)
    (R : Representation ℂ (GL (Fin (s + t)) k) U') (φ : Nonempty (P.Equiv (prod₂ π₁ π₂)))
    (ψ : Nonempty (R.Equiv (prod₂ π₂ π₃))) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃)
    (sP : IsSmooth P) (sR : IsSmooth R) (f₁ : HasFiniteLength π₁) (f₃ : HasFiniteLength π₃)
    (fP : HasFiniteLength P) (fR : HasFiniteLength R) :
    mulR (cl0 P) (cl0 π₃) = mulR (cl0 π₁) (cl0 R) := by
  obtain ⟨a⟩ := ind₂_congr (k := k) (rfl : r + s + t = r + s + t) φ (eqv_refl π₃)
  obtain ⟨b⟩ := ind₂_assoc' (k := k) (rfl : r + s = r + s) (rfl : r + s + t = r + s + t) (rfl : s + t = s + t)
    (Nat.add_assoc r s t).symm π₁ π₂ π₃ s₁ s₂ s₃
  obtain ⟨c⟩ := ind₂_congr (k := k) (Nat.add_assoc r s t).symm (eqv_refl π₁) (eqv_symm ψ)
  have e1 : mulR (cl0 P) (cl0 π₃) = cl0 (prod₂ P π₃) := (h _ _ _ _ P π₃ fP f₃ sP s₃).2.symm
  have e2 : cl0 (prod₂ P π₃) = cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) :=
    class_congr_equiv ⟨(a.trans b).trans c⟩
  have e3 : cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) = cl0 (prod₂ π₁ R) :=
    class_induced_cast (Nat.add_assoc r s t).symm (extTensor π₁ R)
  have e4 : cl0 (prod₂ π₁ R) = mulR (cl0 π₁) (cl0 R) := (h _ _ _ _ π₁ R f₁ fR s₁ sR).2
  exact e1.trans (e2.trans (e3.trans e4))

end GrothendieckAssociativity

open GrothendieckAssociativity

variable (k)

theorem assoc (h : MulCls k) : Assoc k := by
  apply CompanionTheory.Groth.assoc <;> assumption

theorem one : One k := by
  apply CompanionTheory.Groth.one <;> assumption

end PositivityTheory.Groth
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriCoeFlattenDecW

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M



namespace PositivityTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Δ.ms := by
  unfold decW Segment.ms
  rw [← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL (k := k))) := by
  obtain ⟨L, rfl, hs⟩ := H
  unfold msupp
  rw [← tri_coe_flatten_decW]
  exact Multiset.coe_eq_coe.mpr (GlobalTheory.T.perm_flatten_of_shuffle _ _ hs).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL (k := k))) := by
  obtain ⟨h1, _⟩ := H
  unfold wtW msupp
  rw [← h1]
  have e1 : (List.ofFn fun i => decW (Γ i.rev)) = (List.ofFn fun i => Γ i.rev).map decW := by
    rw [List.map_ofFn]
    rfl
  rw [e1, tri_coe_flatten_decW, ← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hL hy hj
  obtain ⟨Δ, hΔ, hx⟩ := hL
  obtain ⟨h', x', hd', ⟨Γ, hΓ, _⟩, _⟩ := id hy
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hw : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hadm c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hsub : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.mp hj
  have hw2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hsub _ hw
  have hsh : InShW (Multiset.map Δ Finset.univ.val) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hadm c.jac x hd Δ hx _ (GlobalTheory.T.ordered_word_letters_cuspidal Γ) hw2
  rw [hΔ.1] at hsh
  refine ⟨(tri_msupp_of_inShW hsh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases heq : 𝔪 = 𝔫
  · exact Or.inl heq
  · right
    have hne : Multiset.map toA 𝔪 ≠ ↑(List.map toA (List.ofFn Γ)) := by
      rw [GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ]
      exact fun e => heq (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
    have hlt := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
      (List.map toA (List.ofFn Γ)) (Multiset.map toA 𝔪) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
      (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW hsh) hne
    rw [GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ, tri_sqLen_map_toA, tri_sqLen_map_toA] at hlt
    exact hlt

end PositivityTheory.Groth

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothOfCls

section

@[expose] public section

namespace PositivityTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hc := H k
  have hm := mulCls k
  have ha := assoc k hm
  have hco := comm k
  have ho := one k
  have hp := prodList k hm
  exact ⟨hc, hm, ha, hco, ho, hp, tri k hc, multOne k hc hm ha hco ho hp, jCls k, jSeg k, altSum k⟩

end PositivityTheory.Groth
end
end
