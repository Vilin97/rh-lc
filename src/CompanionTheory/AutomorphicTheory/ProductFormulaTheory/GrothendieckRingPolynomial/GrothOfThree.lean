module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleCast
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JacquetFunctionalClass
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MultOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlattenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PeelGood

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JhMultSegCl

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SegJ


open Classical in
theorem jhMult_seg_cl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (y : Fin Δ.len → IrrCl (GL (Fin Δ.d) k)) (hd : ∑ _ : Fin Δ.len, Δ.d = Δ.len * Δ.d) :
    jhMult (piTensor fun a => (y a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) =
      if (∀ a, (⟨Δ.d, y a⟩ : IrrGL (k := k)) = Δ.term a) then 1 else 0 := by
  obtain ⟨Φ⟩ := ((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1
    (Z Δ).cl_rep
  let Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep) :=
    piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)
  have hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term
  rw [jhMult_congr_right _ (Φ.trans Ψ)]
  split_ifs with h
  · have hy : ∀ a, y a = (Δ.term a).2 := fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2
    obtain rfl : y = fun a => (Δ.term a).2 := funext hy
    exact jhMult_self hT
  · by_contra hne
    have hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible :=
      GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL (k := k)))
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)
    have hcl := GlobalTheory.T.tensor_product_determines_factor_classes (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep)
      (fun a => (y a).rep) ⟨φ⟩
    refine h fun a => ?_
    have h1 : (Δ.term a).2 = y a := (IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))
    rw [← h1]
    rfl


open Classical in
theorem jm_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    {m : ℕ} (y : Fin m → IrrGL (k := k)) (hy : ∀ a, (y a).1 = Δ.d) (hd : ∑ a, (y a).1 = Δ.len * Δ.d) :
    jm y hd (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) =
      if ∃ h : m = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a) then 1 else 0 := by
  have hm : m = Δ.len := by
    have h1 : ∑ a, (y a).1 = m * Δ.d := by simp [hy]
    exact Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)
  subst hm
  obtain ⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩ :=
    ⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,
      funext fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩
  show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _
  rw [jhMult_seg_cl hA hZ Δ y' hd]
  congr 1
  exact propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩


open Classical in
theorem jmL_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (W : List (IrrGL (k := k))) (hW : ∀ w ∈ W, w.1 = Δ.d) (hl : W.length = Δ.len) :
    jmL W (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) = if W = List.ofFn Δ.term then 1 else 0 := by
  have hy : ∀ a, (W.get a).1 = Δ.d := fun a => hW _ (List.get_mem _ _)
  have hd : ∑ a, (W.get a).1 = Δ.len * Δ.d := by
    rw [Finset.sum_congr rfl fun a _ => hy a]
    simp [hl]
  unfold jmL
  rw [dite_eq_left hd, jm_seg hA hZ Δ W.get hy hd]
  congr 1
  refine propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩
  · refine List.ext_get (by simp [h]) fun n h1 h3 => ?_
    simpa using h2 ⟨n, h1⟩
  · rintro rfl
    exact ⟨List.length_ofFn, fun a => by simp; rfl⟩

theorem vWord_ne (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (S : Finset (Fin Δ.len))
    (hS : S ∈ vSets Δ) (hne : S ≠ ∅) : vWord Δ S ≠ List.ofFn Δ.term := by
  intro H
  rw [vWord, List.ofFn_eq_map] at H
  have H2 := (List.map_injective_iff.2 (GlobalTheory.T.segment_term_injective hA Δ)) H
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)
  have hx : x ∈ S := by
    have : x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse := hxt ▸ List.mem_cons_self ..
    simpa using this
  rw [hxt] at H2
  have h0 := congrArg (fun L => L[0]?) H2
  simp at h0
  have h3 := (Finset.mem_filter.1 hS).2 x hx
  rw [List.getElem?_eq_getElem (by simpa using Δ.len_pos)] at h0
  have h4 := Option.some.inj h0
  apply h3
  rw [h4]
  simp

end SegJ


open SegJ in
variable (k) in
theorem jSeg : JSeg k := by
  intro Z hZ Δ
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hterm : ∀ a, (Δ.term a).1 = Δ.d := fun _ => rfl
  refine ⟨?_, fun S hS hne => ?_⟩
  · rw [jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]
  · rw [jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]
    · intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      rfl
    · simp [vWord]
      rw [← List.length_eq_length_filter_add]
      simp

end CompanionTheory.Groth

end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriCoeFlattenDecW

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M



namespace CompanionTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Δ.ms := by
  have e := GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn Δ.term
  rw [decW, ← e, Multiset.coe_reverse, Segment.ms, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL (k := k))) := by
  obtain ⟨L, rfl, hS⟩ := H
  rw [msupp, ← tri_coe_flatten_decW]
  exact (Multiset.coe_eq_coe.2 (GlobalTheory.T.perm_flatten_of_shuffle _ _ hS)).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL (k := k))) := by
  have e : wtW Γ = (((List.ofFn Γ).reverse).map decW).flatten := by
    rw [wtW, GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, List.map_ofFn]
    try rfl
  rw [e, tri_coe_flatten_decW, Multiset.coe_reverse, ← Fin.univ_val_map, H.1, msupp]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hx hy hm
  obtain ⟨Δ, hΔ, hΔL⟩ := hx
  obtain ⟨h', x', hd', ⟨Γ, hΓ, -⟩, -⟩ := id hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have w1 : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hs : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.1 hm
  have w2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hs _ w1
  have sh : InShW (Finset.univ.val.map Δ) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hA c.jac x hd Δ hΔL (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ) w2
  rw [hΔ.1] at sh
  refine ⟨(tri_msupp_of_inShW sh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases he : 𝔪 = 𝔫
  · exact Or.inl he
  right
  have hL := GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ
  have hne : 𝔪.map toA ≠ (((List.ofFn Γ).map toA : List _) : Multiset _) := by
    rw [hL]
    intro e
    exact he (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
  have key := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
    ((List.ofFn Γ).map toA) (𝔪.map toA) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
    (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW sh) hne
  rw [hL, tri_sqLen_map_toA, tri_sqLen_map_toA] at key
  exact key

end CompanionTheory.Groth

end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriSupportedLe

section

@[expose] public section

open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.tri_bij <;> assumption

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_inj <;> assumption

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_exists <;> assumption

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add (f := _), ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfCls

section

@[expose] public section

namespace CompanionTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hm : MulCls k := by apply mulCls
  have ha : Assoc k := by apply assoc; exact hm
  have hc : Comm k := comm k
  have h1 : One k := by apply one
  have hl : ProdList k := by apply prodList; exact hm
  refine ⟨H k, hm, ha, hc, h1, hl, tri k (H k), ?_, by apply jCls, by apply jSeg, altSum k⟩
  apply multOne <;> first | exact H k | assumption

end CompanionTheory.Groth
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfThree

section

@[expose] public section

namespace CompanionTheory.Groth

theorem groth_of_three (hZ : GlobalTheory.Published.SegmentRepresentation)
    (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.Cos.LUnlinkedIrr k)
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_cls fun k _ _ _ _ => cls_of hZ k (hI k) (H k)

end CompanionTheory.Groth
end
end
