module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.Centred
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.CongrProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PCentred
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsReorderord
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PUnit
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PComb

section

@[expose] public section

namespace PositivityTheory.Gud.Pf

theorem list_symmetric_pair_decomposition {α : Type*} : ∀ (n : ℕ) (l : List (α × ℝ)), l.length = n →
    List.Perm (l.map (fun p => (p.1, -p.2))) l →
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hlen hl
  rcases l with _ | ⟨p, l'⟩
  · exact ⟨[], [], by simp, by simp⟩
  by_cases h0 : p.2 = 0
  · have hp : ((p.1, -p.2) : α × ℝ) = p := Prod.ext rfl (by simp [h0])
    have hl' : List.Perm (l'.map (fun p => (p.1, -p.2))) l' := by
      rw [List.map_cons, hp] at hl
      exact hl.cons_inv
    obtain ⟨a', b', hb', hperm'⟩ := ih l'.length (by simp at hlen; omega) l' rfl hl'
    have hp0 : ((p.1, (0 : ℝ)) : α × ℝ) = p := Prod.ext rfl h0.symm
    refine ⟨p.1 :: a', b', fun q hq => ⟨(hb' q hq).1, List.mem_cons_of_mem _ (hb' q hq).2⟩, ?_⟩
    simp only [List.map_cons, List.cons_append, hp0]
    exact hperm'.cons p
  · have hnp : ((p.1, -p.2) : α × ℝ) ≠ p := by
      intro h
      have h2 := congrArg Prod.snd h
      simp only at h2
      exact h0 (by linarith)
    have hmem : ((p.1, -p.2) : α × ℝ) ∈ p :: l' := hl.subset (by simp)
    have hmem' : ((p.1, -p.2) : α × ℝ) ∈ l' := (List.mem_cons.mp hmem).resolve_left hnp
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem'
    have hmid : List.Perm (p :: (s ++ (p.1, -p.2) :: t)) (p :: (p.1, -p.2) :: (s ++ t)) :=
      List.perm_middle.cons p
    have h1 : List.Perm ((p :: (p.1, -p.2) :: (s ++ t)).map (fun p => (p.1, -p.2)))
        (p :: (p.1, -p.2) :: (s ++ t)) :=
      ((hmid.map _).symm.trans hl).trans hmid
    simp only [List.map_cons, neg_neg, Prod.mk.eta] at h1
    have h2 : List.Perm ((s ++ t).map (fun p => (p.1, -p.2))) (s ++ t) :=
      ((h1.trans (List.Perm.swap ((p.1, -p.2) : α × ℝ) p (s ++ t))).cons_inv).cons_inv
    obtain ⟨a'', b'', hb'', hperm''⟩ :=
      ih (s ++ t).length (by simp only [List.length_cons, List.length_append] at hlen ⊢; omega) (s ++ t) rfl h2
    have hin : ∀ q ∈ b'', q ∈ p :: (s ++ (p.1, -p.2) :: t) := by
      intro q hq
      have hq' := (hb'' q hq).2
      simp only [List.mem_cons, List.mem_append] at hq' ⊢
      tauto
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine ⟨a'', (p.1, -p.2) :: b'', ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨by simp only; linarith, hmem⟩
        · exact ⟨(hb'' q hq).1, hin q hq⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append, neg_neg, Prod.mk.eta]
        exact List.perm_middle.trans ((List.perm_middle.cons _).trans (((hperm''.cons _).cons _).trans
          ((List.Perm.swap p ((p.1, -p.2) : α × ℝ) (s ++ t)).trans hmid.symm)))
    · refine ⟨a'', p :: b'', ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hpos, List.mem_cons_self ..⟩
        · exact ⟨(hb'' q hq).1, hin q hq⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        exact List.perm_middle.trans ((List.perm_middle.cons _).trans (((hperm''.cons _).cons _).trans
          hmid.symm))

theorem comb {α : Type*} (l : List (α × ℝ)) (hl : List.Perm (l.map (fun p => (p.1, -p.2))) l) :
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := list_symmetric_pair_decomposition l.length l rfl hl

theorem perm_ofFn {β : Type*} {h : ℕ} (x : Fin h → β) (l : List β) (hp : List.Perm l (List.ofFn x)) :
    ∃ (y : Fin h → β), List.ofFn y = l ∧ ∃ σ : Equiv.Perm (Fin h), y = fun j => x (σ j) := by
  classical
  have hlen : l.length = h := by rw [hp.length_eq, List.length_ofFn]
  subst hlen
  refine ⟨l.get, List.ofFn_get l, ?_⟩
  have key : ∀ (f : Fin l.length → β) (c : β), Fintype.card {a // f a = c} = (List.ofFn f).count c := by
    intro f c
    rw [Fintype.card_subtype, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map,
      Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun a _ => eq_comm)
  have hcard : ∀ c, Fintype.card {a // l.get a = c} = Fintype.card {b // x b = c} := by
    intro c
    rw [key, key, List.ofFn_get, hp.count_eq]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)),
    funext fun j => (Equiv.ofFiberEquiv_map _ j).symm⟩

end PositivityTheory.Gud.Pf
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.LanglandsClassification.Bridge

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace PositivityTheory.Lit1

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg {Δ : Segment k} {x y : IrrGL (k := k)} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have hn : n = m := hx.deg_eq.symm.trans hy.deg_eq
  subst hn
  obtain ⟨e⟩ := hx.unique hy
  have hab : a = b := Quotient.out_equiv_out.mp ⟨e.symm⟩
  rw [hab]

variable {Lseg : Segment k → IrrGL (k := k)} {L : Multiset (Segment k) → IrrGL (k := k)} (h1 : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
  (h3 : ∀ (𝔪 : Multiset (Segment k)) (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 →
    ∃ hd : ∑ a, (Lseg (Δ a)).1 = (L 𝔪).1, IsCosocle (L 𝔪).rep (prodIrr (fun a => Lseg (Δ a)) hd))



end

end PositivityTheory.Lit1

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PNueq

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_nu_eq {Δ Δ' : Segment k} (hΔ : PositivityTheory.UdReth2.IsCentred Δ) (hΔ' : PositivityTheory.UdReth2.IsCentred Δ')
    {s s' : ℝ} (h : Δ.nu (s : ℂ) = Δ'.nu (s' : ℂ)) : s = s' ∧ Δ = Δ' := by
  have nn : ∀ (Γ : Segment k) (a b : ℂ), (Γ.nu a).nu b = Γ.nu (a + b) := by
    intro Γ a b
    apply GlobalTheory.SmGL.Segment.ext_first
    · show (Γ.first.nu a).nu b = Γ.first.nu (a + b)
      exact GlobalTheory.LocGL.IrrGL.nu_nu _ _ _
    · rfl
  have n0 : ∀ (Γ : Segment k), Γ.nu 0 = Γ := by
    intro Γ
    apply GlobalTheory.SmGL.Segment.ext_first
    · show Γ.first.nu 0 = Γ.first
      exact GlobalTheory.LocGL.IrrGL.nu_zero _
    · rfl
  have pr : ∀ (Γ : Segment k), Γ.Precedes (Γ.nu 1) := by
    intro Γ
    rw [GlobalTheory.SmGL.Segment.precedes_iff]
    refine ⟨1, Nat.one_pos, Γ.len_pos, ?_, ?_⟩
    · show Γ.len < 1 + Γ.len
      omega
    · show Γ.first.nu 1 = Γ.first.nu ((1 : ℕ) : ℂ)
      simp
  have le1 : s ≤ s' := by
    have hp : (Δ.nu (s : ℂ)).Precedes (Δ'.nu ((s' + 1 : ℝ) : ℂ)) := by
      have : Δ'.nu ((s' + 1 : ℝ) : ℂ) = (Δ.nu (s : ℂ)).nu 1 := by
        rw [h, nn]
        push_cast
        rfl
      rw [this]
      exact pr _
    have := PositivityTheory.UdReth2.add_one_le_of_precedes Δ Δ' hΔ hΔ' s (s' + 1) hp
    linarith
  have le2 : s' ≤ s := by
    have hp : (Δ'.nu (s' : ℂ)).Precedes (Δ.nu ((s + 1 : ℝ) : ℂ)) := by
      have : Δ.nu ((s + 1 : ℝ) : ℂ) = (Δ'.nu (s' : ℂ)).nu 1 := by
        rw [← h, nn]
        push_cast
        rfl
      rw [this]
      exact pr _
    have := PositivityTheory.UdReth2.add_one_le_of_precedes Δ' Δ hΔ' hΔ s' (s + 1) hp
    linarith
  have hs : s = s' := le_antisymm le1 le2
  refine ⟨hs, ?_⟩
  subst hs
  have := congrArg (fun Γ => Γ.nu (-(s : ℂ))) h
  simp only [nn, add_neg_cancel, n0] at this
  exact this

theorem eq_of_isLSeg' {Δ : Segment k} {δ δ' : IrrGL (k := k)} (h : IsLSeg Δ δ.rep) (h' : IsLSeg Δ δ'.rep) : δ = δ' :=
  PositivityTheory.Lit1.eq_of_isLSeg h h'

end Local

end PositivityTheory.Gud.Pf

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PReorder

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reorder {h N : ℕ} (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Δ j) (δ j).rep) (hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)) (hs : ∀ j, |s j| < 1 / 2)
    (σ : Equiv.Perm (Fin h)) (hd : ∑ j, ((δ j).nu (s j)).1 = N) (hd' : ∑ j, ((δ (σ j)).nu (s (σ j))).1 = N) :
    Nonempty ((prodIrr (fun j => (δ j).nu (s j)) hd).Equiv (prodIrr (fun j => (δ (σ j)).nu (s (σ j))) hd')) := by
  have hnp : ∀ i j, ¬ ((Δ i).nu ((s i : ℝ) : ℂ)).Precedes ((Δ j).nu ((s j : ℝ) : ℂ)) := by
    intro i j hp
    have h1 := PositivityTheory.UdReth2.add_one_le_of_precedes (Δ i) (Δ j) (hc i) (hc j) (s i) (s j) hp
    have := hs i
    have := hs j
    rw [abs_lt] at *
    linarith
  exact PositivityTheory.PfEss.Zc2.cs_reorderord PositivityTheory.RgGu.NR.ConjDual.irrAdm' (GlobalTheory.RgGu.Holds.lUnlinkedComm_holds k)
    (fun j => (Δ j).nu ((s j : ℝ) : ℂ)) σ (fun j => (δ j).nu (s j)) hd hd'
    (fun i j _ => hnp i j) (fun i j _ => hnp (σ i) (σ j)) (fun j => GlobalTheory.isLSeg_nu (hL j) _)

end PositivityTheory.Gud.Pf

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Fin

open PositivityTheory.Gud.Pf

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def readOff (Γ : Segment k) : Option (IrrGL (k := k) × ℝ) :=
  open Classical in
  if hex : ∃ p : IrrGL (k := k) × ℝ, ∃ Δ : Segment k, PositivityTheory.UdReth2.IsCentred Δ ∧ IsLSeg Δ p.1.rep ∧ Γ = Δ.nu (p.2 : ℂ)
  then some (Classical.choose hex) else none

theorem readOff_nu {Δ : Segment k} {δ : IrrGL (k := k)} (hc : PositivityTheory.UdReth2.IsCentred Δ) (hL : IsLSeg Δ δ.rep) (t : ℝ) :
    readOff (Δ.nu (t : ℂ)) = some (δ, t) := by
  have hex : ∃ p : IrrGL (k := k) × ℝ, ∃ Δ' : Segment k, PositivityTheory.UdReth2.IsCentred Δ' ∧ IsLSeg Δ' p.1.rep ∧
      Δ.nu (t : ℂ) = Δ'.nu (p.2 : ℂ) := ⟨(δ, t), Δ, hc, hL, rfl⟩
  unfold readOff
  rw [dite_eq_left hex]
  obtain ⟨Δ', hc', hL', he⟩ := Classical.choose_spec hex
  obtain ⟨h1, rfl⟩ := eq_of_nu_eq hc hc' he
  have h2 := eq_of_isLSeg' hL hL'
  congr 1
  exact Prod.ext h2.symm h1.symm

theorem tail_step {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V} {h : ℕ}
    (X : Fin h → IrrGL (k := k)) (hd : ∑ j, (X j).1 = N) (φ : π.Equiv (prodIrr X hd)) (F : List (IrrGL (k := k)))
    (hF : List.Perm F (List.ofFn X))
    (hR : ∀ (σ : Equiv.Perm (Fin h)) (hd' : ∑ j, (X (σ j)).1 = N),
      Nonempty ((prodIrr X hd).Equiv (prodIrr (fun j => X (σ j)) hd'))) :
    ∃ (h' : ℕ) (x : Fin h' → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), List.ofFn x = F ∧ Nonempty (π.Equiv (prodIrr x hd)) := by
  obtain ⟨y, hy, σ, rfl⟩ := perm_ofFn X F hF
  have hd' : ∑ j, (X (σ j)).1 = N := by
    rw [Equiv.sum_comp σ (fun j => (X j).1)]
    exact hd
  exact ⟨h, fun j => X (σ j), hd', hy, ⟨φ.trans (hR σ hd').some⟩⟩

end Local

theorem genericUnitaryDualGL_holds : GlobalTheory.Published.GenericUnitaryDualGL := by
  intro k _ _ _ _ _ N V _ _ π hsm hirr hU hgen
  obtain ⟨h, δ, Δ, s, hL, hCC, hs, hd, ⟨φ⟩⟩ :=
    PositivityTheory.RgUd.Exp.genUnitCCOf (fun k => PositivityTheory.RgUd.expBound k) GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
      k N V π hsm hirr hU hgen
  have hcent : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j) := fun j => isCentred_of_unitCC (hL j) (hCC j)
  have hirrP := GlobalTheory.Parabolic.isIrreducible_of_equiv φ hirr
  have hUP := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ hU
  have hsym := segs_symm δ Δ s hL hCC hs hd hirrP hUP
  have e1 : ∀ j, readOff ((Δ j).nu ((s j : ℝ) : ℂ)) = some (δ j, s j) :=
    fun j => readOff_nu (hcent j) (hL j) (s j)
  have e2 : ∀ j, readOff ((Δ j).nu ((-s j : ℝ) : ℂ)) = some (δ j, -s j) :=
    fun j => readOff_nu (hcent j) (hL j) (-s j)
  have hm := congrArg (Multiset.map readOff) hsym
  simp only [Multiset.map_map, Function.comp_def, e1, e2] at hm
  have hm2 : Multiset.map (fun j => (δ j, -s j)) Finset.univ.val =
      Multiset.map (fun j => (δ j, s j)) Finset.univ.val := by
    refine (Multiset.map_injective (Option.some_injective _) ?_).symm
    simpa [Multiset.map_map, Function.comp_def] using hm
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hm2
  set l := List.ofFn (fun j => (δ j, s j)) with hl
  have hperm : (l.map (fun p : IrrGL (k := k) × ℝ => (p.1, -p.2))).Perm l := by
    rw [hl, List.map_ofFn]
    exact hm2
  obtain ⟨a, b, hb, hab⟩ := comb l hperm
  have memL : ∀ p ∈ l, ∃ j, (δ j, s j) = p := by
    intro p hp
    rw [hl, List.mem_ofFn] at hp
    obtain ⟨j, hj⟩ := hp
    exact ⟨j, hj⟩
  have hUL : ∀ j, GlobalTheory.GenericUnitary.IsUnitaryLSeg (δ j) :=
    fun j => ⟨⟨Δ j, hL j⟩, unitarisable_of_unitCC (hL j) (hCC j)⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (x, (0 : ℝ)) ∈ l := hab.subset (List.mem_append_left _ (List.mem_map_of_mem hx))
    obtain ⟨j, hj⟩ := memL _ hx'
    have : δ j = x := congrArg Prod.fst hj
    rw [← this]
    exact hUL j
  · intro p hp
    obtain ⟨j, hj⟩ := memL p (hb p hp).2
    subst hj
    exact ⟨hUL j, (hb _ hp).1, (abs_lt.mp (hs j)).2⟩
  · have hfac : GlobalTheory.GenericUnitary.factors a b =
        (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p : IrrGL (k := k) × ℝ => [p, (p.1, -p.2)])).map
          (fun p : IrrGL (k := k) × ℝ => p.1.nu (p.2 : ℂ)) := by
      simp [GlobalTheory.GenericUnitary.factors, List.map_flatMap, Function.comp_def, IrrGL.nu_zero]
    have hF : (GlobalTheory.GenericUnitary.factors a b).Perm (List.ofFn (fun j => (δ j).nu ((s j : ℝ) : ℂ))) := by
      rw [hfac]
      have := hab.map (fun p : IrrGL (k := k) × ℝ => p.1.nu (p.2 : ℂ))
      rw [hl, List.map_ofFn] at this
      exact this
    exact tail_step (fun j => (δ j).nu ((s j : ℝ) : ℂ)) hd φ _ hF
      (fun σ hd' => reorder δ Δ s hL hcent hs σ hd hd')

end PositivityTheory.Gud.Fin

end
end
end
