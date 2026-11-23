module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZAux
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSumStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleApply

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace PhiLAux

theorem exists_lseg (hs : LSegExists k) : ∃ Lseg : Segment k → IrrGL (k := k), ∀ Δ, IsLSeg Δ (Lseg Δ).rep := by
  choose π hπ using hs
  exact ⟨fun Δ => ⟨Δ.deg, (π Δ).cl⟩, fun Δ => (hπ Δ).of_equiv (equivRep (π Δ))⟩

theorem lfactors_sum {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨hΔ, -⟩, hxΔ⟩ := hx
  rw [← hΔ, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => ((hxΔ a).deg_eq).symm

theorem isL_deg {𝔪 : Multiset (Segment k)} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : N = (𝔪.map Segment.deg).sum := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  rw [← hd, lfactors_sum hx]

theorem isL_cls_unique (hf : LOrderFree k) {𝔪 : Multiset (Segment k)} {x y : IrrGL (k := k)} (hx : IsL 𝔪 x.rep)
    (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have e : n = m := (isL_deg hx).trans (isL_deg hy).symm
  subst e
  exact congrArg (Sigma.mk n) (irrCl_eq_iff.2 (GlobalTheory.T.langlands_classification_order_free_equiv hf 𝔪 _ _ hx hy))

theorem exists_orderedForm (𝔪 : Multiset (Segment k)) : ∃ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 := by
  obtain ⟨h₁, -, -, Δ₁, -, -, hΔ₁, -⟩ := GlobalTheory.T.ordered_forms_interleave_sum CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top 𝔪 0
  exact ⟨h₁, Δ₁, hΔ₁⟩

theorem class_apply_same_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hl : HasFiniteLength π) (c : IrrCl (GL (Fin N) k)) : cl0 π ⟨N, c⟩ = ((jhMult c.rep.ρ π).toNat : ℤ) := by
  unfold cl0
  rw [dite_eq_left hl]
  exact (clsGL_apply π hl c).trans (cls_apply π hl c)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem class_apply_other_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (y : IrrGL (k := k)) (hy : y.1 ≠ N) : cl0 π y = 0 := by
  unfold cl0
  split_ifs with hl
  · rw [clsGL]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨c, rfl⟩; exact hy rfl)
  · rfl

theorem class_product_irreducible_apply {h : ℕ} (x : Fin h → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1) :
    cl0 (prodIrr x (N := ∑ a, (x a).1) rfl) y = ((jhMult y.rep (prodIrr x hd)).toNat : ℤ) := by
  obtain ⟨n, c⟩ := y
  dsimp only at hd
  subst hd
  exact class_apply_same_degree _ (GlobalTheory.T.product_irreducible_finite_length CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top x _) c

theorem sum_sq_le (s : Multiset ℕ) : (s.map fun l => l ^ 2).sum ≤ s.sum ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have h1 : (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
    have h2 := Nat.zero_le (2 * a * s.sum)
    rw [h1]
    linarith

theorem sq_le (𝔪 : Multiset (Segment k)) : CompanionTheory.Groth.sq 𝔪 ≤ (Multiset.card (msupp 𝔪)) ^ 2 := by
  have hc : Multiset.card (msupp 𝔪) = (𝔪.map Segment.len).sum := by
    rw [msupp, Multiset.card_bind]
    simp [Segment.card_ms]
  have hs : CompanionTheory.Groth.sq 𝔪 = ((𝔪.map Segment.len).map fun l => l ^ 2).sum := by
    rw [Multiset.map_map]
    rfl
  rw [hc, hs]
  exact sum_sq_le _

theorem prod_map_toMultiset {M : Type*} [CommMonoid M] {α : Type*} (g : α → M) (s : α →₀ ℕ) :
    ((Finsupp.toMultiset s).map g).prod = s.prod fun a n => g a ^ n := by
  refine Finsupp.induction s ?_ ?_
  · simp
  · intro a n f _ _ ih
    rw [map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
      Multiset.prod_singleton]
    congr 1
    exact (Finsupp.prod_single_index (h := fun x m => g x ^ m) (pow_zero (g a))).symm

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem toR_foldr (l : List (IrrGL (k := k))) :
    toR (l.foldr (fun y a => mulR (sg y) a) (GrothGL.unit k)) = (l.map fun y => toR (sg y)).prod := by
  induction l with
  | nil => simp [toR_unit]
  | cons y l ih => rw [List.foldr_cons, toR_mulR, ih, List.map_cons, List.prod_cons]

theorem ring_class_product_irreducible (hPL : ProdList k) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    toR (cl0 (prodIrr x hd)) = ∏ a, toR (sg (x a)) := by
  rw [hPL h N x hd, toR_foldr, List.map_ofFn, List.prod_ofFn]
  rfl

end PhiLAux

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem phiL_main (hk : Steps k) (h2 : UniTri) :
    ∃ Lseg : Segment k → IrrGL (k := k), (∀ Δ, IsLSeg Δ (Lseg Δ).rep) ∧ Function.Bijective (phiOf Lseg) ∧
      (∀ (𝔫 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔫 x.rep →
        ∃ p : MvPolynomial (Segment k) ℤ, phiOf Lseg p = toR (sg x) ∧
          ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = msupp 𝔫) ∧
      ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
        phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
  classical
  obtain ⟨c, -, -, -, -, hPL, hTri, hMO, -⟩ := hk
  obtain ⟨Lseg, hLseg⟩ := PhiLAux.exists_lseg c.seg
  have hInj : LInjective k := GlobalTheory.T.langlands_injective_of_socle CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top c.soc c.jac
  choose Lm hLm using c.ex
  have hLbij : Function.Bijective Lm := by
    refine ⟨fun 𝔪 𝔫 e => hInj 𝔪 𝔫 (Lm 𝔪) (hLm 𝔪) (by rw [e]; exact hLm 𝔫), fun x => ?_⟩
    obtain ⟨𝔪, h𝔪⟩ := c.exh x
    exact ⟨𝔪, PhiLAux.isL_cls_unique c.free (hLm 𝔪) h𝔪⟩
  let L : Multiset (Segment k) ≃ IrrGL (k := k) := Equiv.ofBijective Lm hLbij
  choose hO Δo hΔo using PhiLAux.exists_orderedForm (k := k)
  have hLF : ∀ 𝔪, LFactors 𝔪 (fun a => Lseg (Δo 𝔪 a)) := fun 𝔪 => ⟨Δo 𝔪, hΔo 𝔪, fun _ => hLseg _⟩
  let f : Multiset (Segment k) → IrrGL (k := k) →₀ ℤ := fun 𝔪 =>
    cl0 (prodIrr (fun a => Lseg (Δo 𝔪 a)) (N := ∑ a, (Lseg (Δo 𝔪 a)).1) rfl)
  have hf1 : ∀ 𝔪, f 𝔪 (L 𝔪) = 1 := by
    intro 𝔪
    have hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔪).1 :=
      (PhiLAux.lfactors_sum (hLF 𝔪)).trans (PhiLAux.isL_deg (hLm 𝔪)).symm
    show cl0 _ (Lm 𝔪) = 1
    rw [PhiLAux.class_product_irreducible_apply _ _ hd, hMO 𝔪 _ _ _ hd (hLF 𝔪) (hLm 𝔪)]
    rfl
  have hf2 : ∀ 𝔪 𝔫, f 𝔪 (L 𝔫) ≠ 0 →
      msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ CompanionTheory.Groth.sq 𝔪 < CompanionTheory.Groth.sq 𝔫) := by
    intro 𝔪 𝔫 h0
    by_cases hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔫).1
    · refine hTri 𝔪 𝔫 _ _ (Lm 𝔫) hd (hLF 𝔪) (hLm 𝔫) fun e => h0 ?_
      show cl0 _ (Lm 𝔫) = 0
      rw [PhiLAux.class_product_irreducible_apply _ _ hd, e]
      rfl
    · exact absurd (PhiLAux.class_apply_other_degree _ _ (Ne.symm hd)) h0
  obtain ⟨hbij, hinv⟩ := h2 _ _ _ L msupp CompanionTheory.Groth.sq (fun C => Multiset.card C ^ 2) f PhiLAux.sq_le hf1 hf2
  let e : (Segment k →₀ ℕ) ≃ Multiset (Segment k) := (Multiset.toFinsupp (α := Segment k)).symm.toEquiv
  have he : ∀ s, e s = Finsupp.toMultiset s := fun s => by
    show (Multiset.toFinsupp (α := Segment k)).symm s = _
    rw [AddEquiv.symm_apply_eq]
    simp
  let G : MvPolynomial (Segment k) ℤ →+ R k :=
    toR.toAddMonoidHom.comp ((Finsupp.linearCombination ℤ f).toAddMonoidHom.comp ((Finsupp.domCongr (M := ℤ) e).toAddMonoidHom.comp
      (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).toAddMonoidHom))
  have hGbij : Function.Bijective G := toR.bijective.comp (hbij.comp ((Finsupp.domCongr e).bijective.comp
    (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).bijective))
  have hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
    intro h N Γ hd
    rw [map_prod, PhiLAux.ring_class_product_irreducible hPL]
    exact Finset.prod_congr rfl fun a _ => phiOf_X _ _
  have hmono : ∀ s : Segment k →₀ ℕ, toR (f (e s)) = s.prod fun n m => toR (sg (Lseg n)) ^ m := by
    intro s
    show toR (cl0 _) = _
    rw [PhiLAux.ring_class_product_irreducible hPL, Finset.prod_eq_multiset_prod,
      ← PhiLAux.prod_map_toMultiset (fun n => toR (sg (Lseg n)))]
    have h1 : Finsupp.toMultiset s = Finset.univ.val.map (Δo (e s)) := (he s).symm.trans (hΔo (e s)).1.symm
    rw [h1, Multiset.map_map]
    rfl
  have hG : ∀ p, phiOf Lseg p = G p := by
    intro p
    refine MvPolynomial.induction_on' p (fun s a => ?_) (fun p q hp hq => ?_)
    · have h1 : G (MvPolynomial.monomial s a) = a • toR (f (e s)) := by
        show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (Finsupp.single s a))) = _
        rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.linearCombination_single, map_zsmul]
      rw [h1, hmono, phiOf, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
    · rw [map_add (f := _), map_add (f := _), hp, hq]
  have hphiG : ⇑(phiOf Lseg) = ⇑G := funext hG
  refine ⟨Lseg, hLseg, hphiG ▸ hGbij, fun 𝔫 x hx => ?_, hprod⟩
  obtain ⟨a, ha, hLa⟩ := hinv 𝔫
  have hxL : x = Lm 𝔫 := PhiLAux.isL_cls_unique c.free hx (hLm 𝔫)
  let cE := AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)
  refine ⟨cE.symm ((Finsupp.domCongr e).symm a), ?_, fun s hs => ?_⟩
  · rw [hG]
    show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (cE (cE.symm ((Finsupp.domCongr e).symm a))))) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hLa, hxL]
    rfl
  · rw [MvPolynomial.mem_support_iff] at hs
    have key : a (e s) = ((Finsupp.domCongr e).symm a : (Segment k →₀ ℕ) →₀ ℤ) s := by
      conv_lhs => rw [← AddEquiv.apply_symm_apply (Finsupp.domCongr e) a]
      rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
    rw [← he s]
    exact ha _ (Finsupp.mem_support_iff.2 (by rw [key]; exact hs))

end CompanionTheory.Groth

end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZBijective

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  have hm : ∀ s : Segment k →₀ ℕ, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial s 1))) =
      if s = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0 := by
    intro s
    obtain ⟨h, Γ, hΓ⟩ := exists_enum s
    rw [← prod_X_of_map s Γ hΓ, hprod h _ Γ rfl, AddEquiv.symm_apply_apply, ell_prod hA hj hJ hAlt Lseg hL, hΓ]
    by_cases hs : s = Finsupp.single Δ 1
    · rw [if_pos ((toMultiset_eq_single_iff s Δ).2 hs), if_pos hs]
    · rw [if_neg (fun h => hs ((toMultiset_eq_single_iff s Δ).1 h)), if_neg hs]
  have hm' : ∀ v, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial v (p.coeff v)))) =
      p.coeff v * (if v = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0) := by
    intro v
    have : MvPolynomial.monomial v (p.coeff v) = p.coeff v • MvPolynomial.monomial v (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, map_zsmul, hm, smul_eq_mul]
  conv_lhs => rw [p.as_sum]

  simp only [map_sum, hm']
  rw [Finset.sum_eq_single (Finsupp.single Δ 1)]
  · simp
  · intro b _ hb; simp [hb]
  · intro hn; rw [MvPolynomial.notMem_support_iff.1 hn]; simp

end CompanionTheory.Groth.GrothendieckPhiBijection

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]


open GrothendieckPhiBijection in
theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Lseg, hL, hbij, hpre, hprod⟩ := phiL_main hk h2
  obtain ⟨hcls, -, -, -, -, -, -, -, hJ, hS, hAlt⟩ := hk
  have key : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) ∧
      ∃ (ε : ℤˣ) (q : MvPolynomial (Segment k) ℤ), (∀ t ∈ q.vars, t.len < Δ.len) ∧
        p = (ε : ℤ) • MvPolynomial.X Δ + q := by
    intro Δ
    obtain ⟨𝔫, h𝔫⟩ := hcls.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp, hsupp⟩ := hpre 𝔫 _ h𝔫
    have hms := msupp_seg hA hcls.jac Z hZ hS Δ h𝔫
    have hce : p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) = 1 := by
      rw [← ell_phiOf hA hcls.jac hJ hAlt Lseg hL hprod Δ p, hp, AddEquiv.symm_apply_apply,
        ell_sg (hS Z hZ Δ).1 (hS Z hZ Δ).2]
    have hc : p.coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have hsq : ((-1 : ℤ) ^ (Δ.len - 1)) * (-1) ^ (Δ.len - 1) = 1 := by
        rw [← mul_pow]; norm_num
      calc p.coeff (Finsupp.single Δ 1)
          = p.coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by rw [hsq, mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, hce, one_mul]
    refine ⟨p, hp, (-1) ^ (Δ.len - 1),
      p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)),
      vars_lt hA p (fun s hs => (hsupp s hs).trans hms), ?_⟩
    have hX : (((-1 : ℤˣ) ^ (Δ.len - 1) : ℤˣ) : ℤ) • (MvPolynomial.X Δ : MvPolynomial (Segment k) ℤ) =
        MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)) := by
      rw [hc, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      push_cast
      rfl
    rw [hX]
    ring
  choose p hp ε q hq hpq using key
  have hψ : Function.Bijective (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) :=
    h1 (Segment k) Segment.len _ fun Δ => ⟨ε Δ, q Δ, hq Δ, by rw [MvPolynomial.eval₂Hom_X']; exact hpq Δ⟩
  have heq : phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) =
      (phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int ((phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩)).comp MvPolynomial.C)
        (((phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p)).comp
          MvPolynomial.C)) r
    · intro Δ
      rw [phiOf_X, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hp Δ]
  rw [heq]
  exact hbij.comp hψ

end CompanionTheory.Groth

end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dite_eq_left h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  have hk : Steps k := H k
  have : Fact (Assoc k) := ⟨hk.2.2.1⟩
  have : Fact (Comm k) := ⟨hk.2.2.2.1⟩
  have : Fact (One k) := ⟨hk.2.2.2.2.1⟩
  let e : MvPolynomial (Segment k) ℤ ≃+* R k := RingEquiv.ofBijective _ (phiZ_bijective hk h1 h2 Z hZ)
  have he : ∀ p, e p = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) p := fun _ => rfl
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · show e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ hs₁ hs₂ h
    show e.symm (toR (clsGL (prod₂ π₁ π₂) h)) = e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, (hk.2.1 r t V W π₁ π₂ h₁ h₂ hs₁ hs₂).2, toR_mulR, map_mul]
  · intro Δ
    show e.symm (toR (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1)) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq, he, phiOf_X]
    rfl

end CompanionTheory.Groth

end
end
end
