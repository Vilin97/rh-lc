module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main
variable {D : D7} {X : HidaSetting D}

theorem stab_of_fix' (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  · have h' : (F0 X u).e (Fin.last _) = (X.Fu u).z := fv_last (lf D (X.Fu u)).fl
    have := hfix (Fin.last _)
    rw [h'] at this
    exact this

theorem fix_X (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a x = x := by
  intro x hx
  have h : Set.EqOn (⇑(a : (VS D).V →ₗ[D.host.E] (VS D).V)) (⇑(LinearMap.id : (VS D).V →ₗ[D.host.E] (VS D).V))
      (Set.range (X.Fu u).e) := by
    rintro _ ⟨i, rfl⟩
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  simpa using LinearMap.eqOn_span h hx

theorem perp_pres (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∀ y ∈ perpS (VS D) (X.Fu u).X, a y ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy x hx
  rw [← fix_X u hfix x hx, hi x y]
  exact hy x hx

theorem ind_exists (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X) (hx : a x.1 ∈ perpS (VS D) (X.Fu u).X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨a x.1, hx⟩ := by
  let f : perpS (VS D) (X.Fu u).X →ₗ[D.host.E] perpS (VS D) (X.Fu u).X :=
    (a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_pres u hi hfix)
  let q := (X.Fu u).X.comap (perpS (VS D) (X.Fu u).X).subtype
  have hq : q ≤ q.comap f := by
    intro x hx
    simp only [q, Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    show a x.1 ∈ (X.Fu u).X
    rw [fix_X u hfix x.1 hx]; exact hx
  refine ⟨Submodule.mapQ q q f hq, fun x hx => ?_⟩
  rw [Submodule.mapQ_apply]
  rfl

end Main
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Main2
variable {D : D7} {X : HidaSetting D}

theorem symm_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a.symm x = x :=
  fun x hx => a.symm_apply_eq.2 (fix_X u hfix x hx).symm

theorem aut_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (y : (VS D).V) : a.symm y ∈ Λ ↔ y ∈ Λ := by
  rw [← GlobalTheory.LoopC.FrEqv.mem_gmap (Λ := Λ) a y, hga]

theorem nlam_of_same (u : D.what₂.Word) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hia : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hib : b ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (hgb : Formalism.HermitianLatticesTheory.gmap b Λ = Λ)
    (hfa : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) (hfb : ∀ c, b ((F0 X u).e c) = (F0 X u).e c)
    (hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, b x - a x ∈ (X.Fu u).X) :
    a⁻¹ * b ∈ NLam Λ (lf D (X.Fu u)) := by
  have happ : ∀ x, (a⁻¹ * b) x = a.symm (b x) := fun x => rfl
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hia) hib, ?_⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · ext y
    rw [GlobalTheory.LoopC.FrEqv.mem_gmap]
    have : (a⁻¹ * b).symm y = b.symm (a y) := by
      apply (a⁻¹ * b).injective
      rw [LinearEquiv.apply_symm_apply, happ, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, aut_iff hgb]
    have h2 := aut_iff hga (a y)
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · have hX : x ∈ (X.Fu u).X := by
      have hle : Xflag (lf D (X.Fu u)) (j + 1) ≤ (X.Fu u).X :=
        Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
      exact hle hx
    rw [happ, fix_X u hfb x hX, symm_fix u hfa x hX, sub_self]
    exact zero_mem _
  · have hp : x ∈ perpS (VS D) (X.Fu u).X := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact fun y hy => hx y hy
    have e : (a⁻¹ * b) x - x = a.symm (b x - a x) := by
      rw [happ, map_sub, LinearEquiv.symm_apply_apply]
    rw [e, symm_fix u hfa _ (hsame x hp)]
    exact hsame x hp

end Main2
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fibCardC : FibCardC := by
  intro D large₂ X Y u hStd t₀ s hs
  show (s.card : ℝ) * ((Nat.card (autLz D (X.Fu u) t₀.lam') : ℝ))⁻¹ ≤ 1
  by_cases hfin : Finite (autLz D (X.Fu u) t₀.lam')
  swap
  · have : Infinite (autLz D (X.Fu u) t₀.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]; simp
  have H : ∀ t : s, ∃ a : (VS D).V ≃ₗ[D.host.E] (VS D).V, a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap a t₀.lam' = t₀.lam' ∧ (∀ c, a ((F0 X u).e c) = (F0 X u).e c) ∧ t₀.lam' = t.1.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u)), t.1.lin = n * t₀.lin * a * n' := by
    intro t
    obtain ⟨hl, n, a, hn, ha, hga, hfa, n', hn', he⟩ :=
      GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hStd t₀ t.1 (hs t.1 t.2).1 (hs t.1 t.2).2
    exact ⟨a, ha, hga, hfa, hl, n, hn, n', hn', he⟩
  choose A hA using H
  have Hφ : ∀ t : s, ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X)
      (hx : A t x.1 ∈ perpS (VS D) (X.Fu u).X), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨A t x.1, hx⟩ :=
    fun t => ind_exists u (hA t).1 (hA t).2.2.1
  choose Φ hΦ using Hφ
  have hmem : ∀ t, Φ t ∈ autLz D (X.Fu u) t₀.lam' :=
    fun t => ⟨A t, stab_of_fix' u (hA t).1 (hA t).2.2.1, (hA t).2.1, hΦ t⟩
  let f : s → autLz D (X.Fu u) t₀.lam' := fun t => ⟨Φ t, hmem t⟩
  have hinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hΦe : Φ t₁ = Φ t₂ := congrArg Subtype.val h12
    obtain ⟨hi1, hg1, hf1, hl1, n₁, hn₁, n₁', hn₁', he1⟩ := hA t₁
    obtain ⟨hi2, hg2, hf2, hl2, n₂, hn₂, n₂', hn₂', he2⟩ := hA t₂
    have hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, A t₂ x - A t₁ x ∈ (X.Fu u).X := by
      intro x hx
      have p1 := perp_pres u hi1 hf1 x hx
      have p2 := perp_pres u hi2 hf2 x hx
      have k1 := hΦ t₁ ⟨x, hx⟩ p1
      have k2 := hΦ t₂ ⟨x, hx⟩ p2
      rw [hΦe, k2] at k1
      have := (Submodule.Quotient.eq _).1 k1
      rw [Submodule.mem_comap] at this
      simpa using this
    have hm := nlam_of_same u hi1 hi2 hg1 hg2 hf1 hf2 hsame
    apply Subtype.ext
    apply GlobalTheory.TypeAsm.eqC_holds D X Y u t₁.1 t₂.1
    · rw [← (hs t₁.1 t₁.2).1, ← (hs t₂.1 t₂.2).1]
    · rw [← hl1, ← hl2]
    · refine ⟨n₂ * n₁⁻¹, ?_, n₁'⁻¹ * ((A t₁)⁻¹ * A t₂) * n₂', ?_, ?_⟩
      · rw [← (hs t₁.1 t₁.2).1]; exact Formalism.L2.SG.Pf.nlam_mul hn₂ (Formalism.L2.SG.Pf.nlam_inv hn₁)
      · rw [← hl1]; exact Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hn₁') hm) hn₂'
      · rw [he1, he2]; group
  have hcard : Nat.card s ≤ Nat.card (autLz D (X.Fu u) t₀.lam') := Nat.card_le_card_of_injective f hinj
  have hs' : Nat.card s = s.card := by simp
  rw [hs'] at hcard
  rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u) t₀.lam')) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Nat.card (autLz D (X.Fu u) t₀.lam') := by exact_mod_cast hpos
    rw [← div_eq_mul_inv, div_le_one hp]; exact_mod_cast hcard

end GlobalTheory.TypeAsm.FibCard
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAutStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.frameClass_termCount_le_card_aut : GlobalTheory.TypeAsm.FibCardC := by
  first | exact @GlobalTheory.TypeAsm.FibCard.fibCardC | exact GlobalTheory.TypeAsm.FibCard.fibCardC | (intros; apply GlobalTheory.TypeAsm.FibCard.fibCardC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum

section

@[expose] public section

open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClasses

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_pairs_le_classes_pf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)),
    (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) →
    (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) →
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  intro D large₂ X Y u hS W HW he Λ h hh Sf hSf hη
  obtain ⟨hK, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hlam : ∀ p ∈ Sf, p.2.lam = Λ ∧ p.2.lam' = p.1.lam' := by
    intro p hp
    obtain ⟨hl, hl', -⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, (hSf p hp).1.2.2⟩
    exact ⟨hl.symm.trans (hSf p hp).2, hl'.symm⟩
  have hL : ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) =
      ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (clsOm Y u Λ (frCls Λ p.1) * clsOm Y u Λ (frCls Λ p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [clsOm_frCls hK Λ p.1 (hSf p hp).2, clsOm_frCls hK Λ p.2 (hlam p hp).1]
  rw [hL]
  generalize hT1 : Sf.image (fun p => frCls Λ p.1) = T₁
  generalize hT2 : Sf.image (fun p => frCls Λ p.2) = T₂
  refine GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (GTu Y u) _ Sf (frCls Λ)
    (fun t => wRow D (X.Fu u) t.lam') (clsOm Y u Λ) T₁ T₂ ?_ (clsOm_nonneg Y u Λ hK) ?_ ?_ ?_
  · intro t
    show 0 ≤ wRow D (X.Fu u) t.lam'
    unfold wRow; positivity
  · intro p hp
    subst hT1 hT2
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  · intro p hp q hq h1 hc
    have hrel2 : p.2 ∈ relSet Y u := (hSf p hp).1.2.1
    have hrelq : q.2 ∈ relSet Y u := (hSf q hq).1.2.1
    have hhe : h p.2 = h q.2 := by
      have e := hη p hp q hq
      rw [h1] at e
      have e2 := congrArg (fun g => (h q.1)⁻¹ * g) e
      simp only [inv_mul_cancel_left] at e2
      exact inv_injective e2
    have hfe := (frCls_eq_iff hK Λ p.2 q.2).1 hc
    have hl : p.2.lam = q.2.lam := ((hlam p hp).1).trans ((hlam q hq).1).symm
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS p.2 hrel2
    have hfe' : GlobalTheory.DegAsm.FrEqv (F0 X u) p.2.lam (Ft p.2) (Ft q.2) := by rw [(hlam p hp).1]; exact hfe
    have := GlobalTheory.T.term_determined_by_frameClass_and_isometry D large₂ X Y u hS W HW he p.2 q.2 ⟨N, hN⟩ hl hfe' (h p.2) (hh p.2 hrel2)
      (by rw [hhe]; exact hh q.2 hrelq)
    exact Prod.ext h1 this
  · intro b
    have gen : ∀ s : Finset (GTu Y u), (∀ t ∈ s, t.lam = Λ ∧ frCls Λ t = b) →
        ∑ a ∈ s, wRow D (X.Fu u) a.lam' ≤ 1 := by
      intro s hmem
      rcases s.eq_empty_or_nonempty with he0 | ⟨t₀, ht₀⟩
      · rw [he0, Finset.sum_empty]; exact zero_le_one
      obtain ⟨hl0, hb0⟩ := hmem t₀ ht₀
      have hrel : ∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t) := by
        intro t ht
        obtain ⟨hl, hb⟩ := hmem t ht
        refine ⟨hl0.trans hl.symm, ?_⟩
        rw [hl0]
        exact (frCls_eq_iff hK Λ t₀ t).1 (hb0.trans hb.symm)
      have hw : ∀ t ∈ s, wRow D (X.Fu u) t.lam' = wRow D (X.Fu u) t₀.lam' := by
        intro t ht
        obtain ⟨hl, hf⟩ := hrel t ht
        rw [(GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hS t₀ t hl hf).1]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      exact GlobalTheory.T.frameClass_termCount_le_card_aut D large₂ X Y u hS t₀ s hrel
    refine gen _ fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_image] at ht
    obtain ⟨⟨p, hp, rfl⟩, ht2⟩ := ht
    exact ⟨(hSf p hp).2, ht2⟩

end GlobalTheory.TypeAsm.PerRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClassesStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)), (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)), (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) → (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) → ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤ (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  first | exact @GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | exact GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | (intros; apply GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf <;> assumption)
end
end
