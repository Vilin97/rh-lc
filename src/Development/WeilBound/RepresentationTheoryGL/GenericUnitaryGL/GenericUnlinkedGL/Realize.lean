module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegGenNu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_after {n : ℕ} (a : Fin n) :
    ∑ b ∈ Finset.univ.filter (fun b => a < b), 1 = (Fin.rev a : ℕ) := by
  have h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  rw [h]
  simp [Fin.val_rev]
  omega

theorem isLSeg_fine (G : Segment k) (a : Fin G.len) :
    IsLSeg (topCut G (fun _ => 1) (fun _ => one_pos) a) (dec G a).rep := by
  have hc : (dec G a).IsCusp := G.isCusp_term _
  have e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc := by
    refine Segment.ext_first ?_ rfl
    show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)
    rw [card_after]
  rw [e]
  exact (single_spec hc).2.1

theorem exists_cut (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) :
    ∃ Γ : Fin G.len → Segment k, IsTopCut G' Γ ∧ ∀ a, IsLSeg (Γ a) (dec G a).rep := by
  have hd : ∑ a, (dec G a).1 = x.1 := (sum_dec G).trans h.deg_eq
  have hpos : ∀ a, 0 < (dec G a).1 := fun a => (G.isCusp_term _).1
  have h1 : jm (dec G) hd x.rep = 1 :=
    (hJ G x.rep h _ (dec G) hd hpos).1
      ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩
  by_contra hn
  have h0 := (hJ G' x.rep h' _ (dec G) hd hpos).2 hn
  rw [h1] at h0
  exact one_ne_zero h0

theorem card_le_len {G : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut G Γ) : s ≤ G.len := by
  rw [← h.1]
  calc s = ∑ _ : Fin s, 1 := by simp
    _ ≤ ∑ a, (Γ a).len := Finset.sum_le_sum fun a _ => (Γ a).len_pos

theorem first_eq (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) : G.first = G'.first := by
  obtain ⟨Γ, hΓ, hL⟩ := exists_cut hJ h h'
  obtain ⟨Γ', hΓ', -⟩ := exists_cut hJ h' h
  have hle := card_le_len hΓ
  have hle' := card_le_len hΓ'
  have hlen : G.len = G'.len := le_antisymm hle hle'
  have hpos := G.len_pos
  let l : Fin G.len := ⟨G.len - 1, by omega⟩
  have hl1 : (Γ l).len = 1 := by
    by_contra hne
    have h2 : 1 < (Γ l).len := by have := (Γ l).len_pos; omega
    have hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len :=
      Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩
    rw [hΓ.1, ← hlen] at hlt
    simp at hlt
  have hb : below Γ l = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (l : ℕ) < b := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    have h4 := b.2
    have h5 : (l : ℕ) = G.len - 1 := rfl
    omega
  have hf : (Γ l).first = G'.first := by
    rw [hΓ.2 l, hb]
    simp
  have e : Γ l = Segment.single G'.first G'.isCusp_first := Segment.ext_first hf hl1
  have h6 : IsLSeg (Γ l) G'.first.rep := by
    rw [e]
    exact (single_spec _).2.1
  have h7 : dec G l = G.first := by
    have h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0 := by
      simp only [Fin.val_rev, l]
      omega
    show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first
    rw [h8]
    simp
  rw [← h7]
  exact eq_of_isLSeg (hL l) h6

theorem lSegGeneric_of_nuPair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : Zc.LSegJacquet k)
    (hP : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.LSegGeneric k := by
  intro Δ N V _ _ π hπ
  by_contra hg
  obtain ⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩ :=
    hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg
  have hpos : ∀ a, 0 < (![α, β] a).1 := by
    intro a
    fin_cases a
    · exact hα
    · exact hβ
  have hpos' : ∀ a, 0 < (![β', α.nu 1] a).1 := by
    intro a
    fin_cases a
    · exact hββ ▸ hβ
    · exact hα
  have hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![α, β] hd hpos).2 hn
    rw [h0] at h1
    simp at h1
  have hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn
    rw [h0] at h2
    simp at h2
  obtain ⟨Γ, hΓ, hL⟩ := hcut
  obtain ⟨Γ', hΓ', hL'⟩ := hcut'
  have e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep := GlobalTheory.isLSeg_nu (hL 0) 1
  have e2 : IsLSeg (Γ' 1) (α.nu 1).rep := hL' 1
  have e3 : (Γ 0).first.nu 1 = (Γ' 1).first := first_eq hJ e1 e2
  have hb : below Γ' 1 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (1 : Fin 2) < b := (Finset.mem_filter.1 hb).2
    exact absurd h3 (by omega)
  rw [hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu] at e3
  have e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    simpa using e3
  have e5 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4
  omega

end GlobalTheory.CompanionTheory.SegGenNu

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPairStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.segment_generic_of_jacquet_nu_pair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.LSegGeneric k := by
  first | exact @GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | exact GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | (intros; apply GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu

namespace GlobalTheory.CompanionTheory.SegLayers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun a b h =>
  Fin.ext ((IrrGL.nu_natCast_inj (x := Δ.first) Δ.d_pos).1 h)

theorem ms_nodup (Δ : Segment k) : Δ.ms.Nodup :=
  Multiset.Nodup.map (term_injective Δ) Finset.univ.nodup

theorem ncard_carrier (Δ : Segment k) : Δ.carrier.ncard = Δ.len := by
  rw [Segment.carrier, ← Set.image_univ, Set.ncard_image_of_injective _ (term_injective Δ)]
  simp

theorem ms_le {Δ : Segment k} {s : Multiset (IrrGL (k := k))} (h : ∀ x ∈ Δ.carrier, x ∈ s) : Δ.ms ≤ s :=
  (Multiset.le_iff_subset (ms_nodup Δ)).2 fun _ hx => h _ (Segment.mem_ms.1 hx)

theorem exists_longest {s : Multiset (IrrGL (k := k))} {y : IrrGL (k := k)} (hy : y ∈ s) (hc : y.IsCusp) :
    ∃ Γ : Segment k, (∀ x ∈ Γ.carrier, x ∈ s) ∧
      ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len := by
  classical
  let P : ℕ → Prop := fun l => ∃ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) ∧ D.len = l
  have hb : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Multiset.card s := fun D hD => by
    rw [← Segment.card_ms]
    exact Multiset.card_le_card (ms_le hD)
  have h1 : P 1 := ⟨Segment.single y hc, fun x hx => by
    rw [Segment.carrier_single] at hx
    exact hx ▸ hy, rfl⟩
  have h1' : 1 ≤ Multiset.card s := by
    obtain ⟨D, hD, e⟩ := h1
    exact e ▸ hb D hD
  obtain ⟨Γ, hΓ, e⟩ := Nat.findGreatest_spec h1' h1
  exact ⟨Γ, hΓ, fun D hD => e ▸ Nat.le_findGreatest (hb D hD) ⟨D, hD, rfl⟩⟩

theorem not_linked_of_longest {s : Multiset (IrrGL (k := k))} {Γ D : Segment k} (hΓ : ∀ x ∈ Γ.carrier, x ∈ s)
    (hm : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len) (hD : ∀ x ∈ D.carrier, x ∈ s) :
    ¬ Γ.Linked D := by
  rintro ⟨⟨U, hU⟩, -, h2⟩
  have h3 : U.len ≤ Γ.len := hm U fun x hx => by
    rw [hU] at hx
    exact hx.elim (hΓ x) (hD x)
  have h4 : Γ.carrier ⊂ U.carrier := by
    rw [hU]
    exact ⟨Set.subset_union_left, fun h => h2 (Set.subset_union_right.trans h)⟩
  have h5 := Set.ncard_lt_ncard h4 (Set.finite_range U.term)
  rw [ncard_carrier, ncard_carrier] at h5
  omega

theorem exists_unlinked (n : ℕ) : ∀ s : Multiset (IrrGL (k := k)), Multiset.card s = n → (∀ y ∈ s, y.IsCusp) →
    ∃ m : Multiset (Segment k), (∀ D ∈ m, ∀ D' ∈ m, ¬ D.Linked D') ∧ m.bind Segment.ms = s := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨y, hy⟩
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨Γ, hΓ, hm⟩ := exists_longest hy (hs y hy)
    have hle := ms_le hΓ
    have hsub : ∀ x ∈ s - Γ.ms, x ∈ s := fun x hx => Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    have hcard : Multiset.card (s - Γ.ms) < n := by
      have h1 := Multiset.card_sub hle
      have h2 := Multiset.card_le_card hle
      have h3 := Γ.len_pos
      rw [Segment.card_ms] at h1 h2
      omega
    obtain ⟨m, hu, hb⟩ := ih _ hcard _ rfl fun x hx => hs x (hsub x hx)
    have hin : ∀ D ∈ m, ∀ x ∈ D.carrier, x ∈ s := fun D hD x hx =>
      hsub x (hb ▸ Multiset.mem_bind.2 ⟨D, hD, Segment.mem_ms.2 hx⟩)
    have hΓD : ∀ D ∈ m, ¬ Γ.Linked D := fun D hD => not_linked_of_longest hΓ hm (hin D hD)
    refine ⟨Γ ::ₘ m, fun D hD D' hD' => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hD with e | e₁ <;> rcases Multiset.mem_cons.1 hD' with e' | e₂
      · rw [e, e']
        exact Segment.not_linked_self _
      · rw [e]
        exact hΓD _ e₂
      · rw [e']
        exact fun h => hΓD _ e₁ h.symm
      · exact hu _ e₁ _ e₂
    · rw [Multiset.cons_bind, hb]
      exact add_tsub_cancel_of_le hle

theorem unlinkedLayers (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UnlinkedLayers k := by
  intro s hs
  obtain ⟨m, hu, hb⟩ := exists_unlinked _ s rfl hs
  have hmem : ∀ i : Fin m.toList.length, m.toList.get i ∈ m := fun i =>
    Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨m.toList.length, m.toList.get, fun i j _ => hu _ (hmem i) _ (hmem j), ?_⟩
  have h1 : (Finset.univ.val.map m.toList.get : Multiset (Segment k)) = m := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  conv_rhs => rw [← hb, ← h1]
  simp [Multiset.bind, Multiset.map_map, Function.comp_def]

end GlobalTheory.CompanionTheory.SegLayers

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHoldStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unlinked_layers_hold : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], UnlinkedLayers k := by
  first | exact @GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | exact GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | (intros; apply GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.Realize

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_map_fst_ms (Δ : Segment k) : (Δ.ms.map Sigma.fst).sum = Δ.deg := by
  rw [Segment.ms, Multiset.map_map, ← Δ.sum_term_fst]
  rfl

theorem unlinkedRealize_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : GlobalTheory.BZSeg.LUnlinkedIrr k)
    (hG : GlobalTheory.BZSeg.LSegGeneric k) (hP : GlobalTheory.BZMir.Leib.GenericProdIff k) : UnlinkedRealize k := by
  intro N s hs hN
  obtain ⟨h, Δ, hun, hbind⟩ := GlobalTheory.T.unlinked_layers_hold k s hs
  choose π hπ using fun i => GlobalTheory.T.exists_segment_representation hA (Δ i)
  let x : Fin h → IrrGL (k := k) := fun i => IrrGL.of (π i).ρ (π i).smooth (π i).irr
  have hx : ∀ i, IsLSeg (Δ i) (x i).rep := fun i => (hπ i).of_equiv (IrrGL.equivOf _ _ _)
  have hd : ∑ a, (x a).1 = N := by
    rw [← hN, ← hbind, Multiset.map_bind, Multiset.sum_bind]
    change ∑ a, (Δ a).deg = _
    rw [Finset.sum_eq_multiset_sum]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (sum_map_fst_ms (Δ i)).symm
  have hirr : (prodIrr x hd).IsIrreducible :=
    hL h N Δ x hd (fun i j => if e : i = j then e ▸ Segment.not_linked_self _ else hun i j e) hx
  refine ⟨h, Δ, x, hd, hun, hx, ?_, ?_⟩
  · have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (t := fun i => (Δ i).ms)
      (fun i => (hx i).hasSupport) hirr (IsSubquotient.refl _)
    rwa [show (∑ i, (Δ i).ms) = s from hbind] at this
  · exact (hP h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
      (fun a => (x a).2.rep.smooth)).2 fun i => hG (Δ i) _ _ _ (hx i)

theorem unlinkedRealize (hJ : Zc.LSegJacquet k) (hN : GlobalTheory.BZSeg.NuPair k) : UnlinkedRealize k :=
  unlinkedRealize_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k hJ PositivityTheory.Geo.geometricLemmaFiltration hN)
    (GlobalTheory.T.segment_generic_of_jacquet_nu_pair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hJ hN)
    (GlobalTheory.T.whittaker_heredity_generic_product k (PositivityTheory.rg.gu.hered2.whitHeredity_all k))

end GlobalTheory.RgGu

end
end
end
