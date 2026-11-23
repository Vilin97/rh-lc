module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMapStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsioStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalization

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem W2.isUnit_of_fst_gh {l : ℕ} [Fact l.Prime] {L : Type} [CommRing L] (x : W2 l L) (h0 : IsUnit x.fst)
    (h1 : IsUnit (W2.gh x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  refine isUnit_iff_exists_inv.2 ⟨⟨(↑u⁻¹ : L), -(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹⟩, ?_⟩
  refine W2.ext ?_ ?_
  · change x.fst * (↑u⁻¹ : L) = 1
    rw [← hu]; simp
  · change x.fst ^ l * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) + (↑u⁻¹ : L) ^ l * x.snd +
      (l : L) * x.snd * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) = 0
    have hg : (↑v⁻¹ : L) * (x.fst ^ l + (l : L) * x.snd) = 1 := by
      change (↑v⁻¹ : L) * W2.gh x = 1
      rw [← hv]; simp
    linear_combination (-(↑u⁻¹ : L) ^ l * x.snd) * hg

theorem delta_localization (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (M : Submonoid A) (hM : ∀ x ∈ M, D.φ x ∈ M) :
    ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  let s0 : A →+* W2 l (Localization M) := (W2.map (algebraMap A (Localization M))).comp (deltaSectionToWittLengthTwo D)
  have hs0 : ∀ m : M, IsUnit (s0 m) := fun m => by
    apply W2.isUnit_of_fst_gh
    · exact IsLocalization.map_units (Localization M) m
    · have : W2.gh (s0 m) = algebraMap A (Localization M) (D.φ m) := by
        rw [D.φ_eq]; change (algebraMap A _ m) ^ l + (l : Localization M) * algebraMap A _ (D.δ m) = _
        simp
      rw [this]
      exact IsLocalization.map_units (Localization M) (⟨D.φ m, hM m m.2⟩ : M)
  let s : Localization M →+* W2 l (Localization M) := IsLocalization.lift hs0
  have hsa : ∀ a : A, s (algebraMap A _ a) = s0 a := fun a => IsLocalization.lift_eq hs0 a
  have hsec : ∀ y, (s y).fst = y := fun y => by
    have : (W2.fstHom.comp s : Localization M →+* Localization M) = RingHom.id _ :=
      IsLocalization.ringHom_ext M (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [hsa]; rfl)
    exact RingHom.congr_fun this y
  refine ⟨deltaStructureOfWittLengthTwoSection s hsec, fun a => ?_⟩
  change algebraMap A _ (D.δ a) = (s (algebraMap A _ a)).snd
  rw [hsa]; rfl

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalizationStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_deltaRingStructure_localization : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (M : Submonoid A), (∀ x ∈ M, D.φ x ∈ M) → ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  first | exact @GlobalTheory.BSP.delta_localization | exact GlobalTheory.BSP.delta_localization | (intros; apply GlobalTheory.BSP.delta_localization <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMap

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ringHom_eq_of_isCompl (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C) (hc : IsCompl i J) (hH : IsHausdorff JC C)
    (h h' : Q →+* C) (hJ : J.map (h.comp i) ≤ JC) (he : h.comp i = h'.comp i) : h = h' := by
  have mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n := by
    intro g hg n y hy
    have h1 : g y ∈ ((J ^ n).map i).map g := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hg n h1
  have hJ' : J.map (h'.comp i) ≤ JC := by rwa [← he]
  ext x
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha⟩ := hc.surj x n
  have e1 : h x - h' x = h (x - i a) - h' (x - i a) := by
    have : h (i a) = h' (i a) := RingHom.congr_fun he a
    simp only [map_sub, this]; ring
  rw [SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMapStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsHausdorff JC C → ∀ (h h' : Q →+* C), J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h = h' := by
  first | exact @GlobalTheory.BSP.ringHom_eq_of_isCompl | exact GlobalTheory.BSP.ringHom_eq_of_isCompl | (intros; apply GlobalTheory.BSP.ringHom_eq_of_isCompl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrism

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem locAway_φ_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) :
    ∀ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f),
      D.φ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f) := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    exact Submonoid.subset_closure ⟨m + 1, by simp only [Function.iterate_succ_apply']⟩
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem locAway_iterate_sub_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (m : ℕ) :
    D.φ^[m] f - f ^ (l ^ m) ∈ Ideal.span {(l : A)} := by
  rw [← Ideal.Quotient.eq]
  induction m with
  | zero => simp
  | succ m ih =>
    have hl0 : ((l : A ⧸ Ideal.span {(l : A)})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [Function.iterate_succ_apply', D.φ_eq, map_add (f := _), map_mul, map_pow, ih, map_natCast, hl0, zero_mul,
      add_zero, map_pow, map_pow, ← pow_mul, pow_succ]

theorem locAway_dvd_mod {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (J : Ideal A)
    (hl : (l : A) ∈ J) (n : ℕ) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f), ∃ (k : ℕ) (t : A), f ^ k - s * t ∈ J ^ n := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    have h1 : f ^ (l ^ m) - D.φ^[m] f ∈ J := by
      rw [← neg_sub, neg_mem_iff]
      exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 hl)) (locAway_iterate_sub_mem D f m)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (f ^ (l ^ m)) (f ^ (l ^ m) - D.φ^[m] f) n
    refine ⟨l ^ m * n, t, ?_⟩
    have e : f ^ (l ^ m * n) - D.φ^[m] f * t = (f ^ (l ^ m) - D.φ^[m] f) ^ n := by
      rw [pow_mul]
      have e2 : f ^ l ^ m - (f ^ l ^ m - D.φ^[m] f) = D.φ^[m] f := by ring
      rw [e2] at ht
      linear_combination ht
    rw [e]; exact Ideal.pow_mem_pow h1 n
  | one => exact ⟨0, 1, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, t1, h1⟩ := hx
    obtain ⟨k2, t2, h2⟩ := hy
    refine ⟨k1 + k2, t1 * t2, ?_⟩
    have e : f ^ (k1 + k2) - x * y * (t1 * t2) = f ^ k1 * (f ^ k2 - y * t2) + y * t2 * (f ^ k1 - x * t1) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)

theorem locAway_units {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} (g : Hom B C) (f : B.A)
    (hu : IsUnit (g.f f)) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f), IsUnit (g.f s) := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      show IsUnit (g.f (B.D.φ^[m + 1] f))
      change IsUnit (g.f (B.D.φ^[m] f)) at ih
      rw [Function.iterate_succ_apply', g.f_φ]
      exact ih.map C.D.φ
  | one => rw [map_one]; exact isUnit_one
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem GenAway₂ : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A),
    GenAway B f d → Nonempty (LocP B f d) := by
  intro l _ R _ B f d hg
  set M := Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f) with hM
  have hfM : f ∈ M := Submonoid.subset_closure ⟨0, rfl⟩
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_localization l B.A B.D M (locAway_φ_mem B.D f)
  obtain ⟨hIL, hdnz, N, hN⟩ := GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion l R B f d hg M hfM
  set J : Ideal (Localization M) := Ideal.span {(l : Localization M)} ⊔
    Ideal.span {algebraMap B.A (Localization M) d} with hJdef
  have hJ : (JJ B).map (algebraMap B.A (Localization M)) = J := by
    rw [JJ, Ideal.map_sup, hIL, Ideal.map_span, Set.image_singleton, map_natCast]
  have hJfg : J.FG := Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)
  obtain ⟨Q, _, i, hi⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ J hJfg
  have hlJ : (l : Localization M) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q i J hi hlJ DL
  obtain ⟨hqnz, hqN⟩ := GlobalTheory.T.adic_completion_regular_and_torsion_bounded l _ Q i (algebraMap B.A (Localization M) d) N hdnz hN hi
  set g : B.A →+* Q := i.comp (algebraMap B.A (Localization M)) with hgdef
  have hgδ : ∀ x, g (B.D.δ x) = DQ.δ (g x) := fun x => by
    simp only [hgdef, RingHom.comp_apply]; rw [hDL x, hDQ]
  have hIg : B.I.map g = Ideal.span {g d} := by
    rw [hgdef, ← Ideal.map_map, hIL, Ideal.map_span, Set.image_singleton]; rfl
  have hIle : B.I ≤ (Ideal.span {g d}).comap g := Ideal.map_le_iff_le_comap.1 hIg.le
  have hJi : J.map i = Ideal.span {(l : Q)} ⊔ Ideal.span {g d} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      map_natCast]; rfl
  have hcomp : IsAdicComplete (Ideal.span {(l : Q)} ⊔ Ideal.span {g d}) Q := by
    have := hi.complete; rwa [hJi] at this
  have hgφ : g.comp B.D.φ = DQ.φ.comp g := RingHom.ext fun x => Delta.map_φ_of_map_δ B.D DQ g hgδ x
  have hlmem : (l : Q) ∈ Ideal.span {g d} ⊔ (Ideal.span {g d}).map DQ.φ := by
    have h := Ideal.mem_map_of_mem g B.l_mem
    have hgm : (B.I.map B.D.φ).map g = (B.I.map g).map DQ.φ := by
      rw [Ideal.map_map, Ideal.map_map, hgφ]
    rwa [map_natCast, Ideal.map_sup, hgm, hIg] at h
  have hbdd : ∃ n : ℕ, ∀ x : Q ⧸ Ideal.span {g d}, (∃ m : ℕ, (l : Q ⧸ Ideal.span {g d}) ^ m * x = 0) →
      (l : Q ⧸ Ideal.span {g d}) ^ n * x = 0 := by
    refine ⟨N, fun x ⟨m, hm⟩ => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
    exact hqN y m hm
  let Qo : Obj l R :=
    { A := Q
      D := DQ
      I := Ideal.span {g d}
      inv := invertible_span_singleton hqnz
      complete := hcomp
      l_mem := hlmem
      bdd := hbdd
      str := (Ideal.quotientMap (Ideal.span {g d}) g hIle).comp B.str }
  let inl : Hom B Qo :=
    { f := g
      f_δ := hgδ
      f_I := fun x hx => hIle hx
      f_str := fun r x h => by
        show _ = Ideal.quotientMap (Ideal.span {g d}) g hIle (B.str r)
        rw [← h, Ideal.quotientMap_mk] }
  have hlu : ∀ s : M, IsUnit (g s) := fun s => (IsLocalization.map_units (Localization M) s).map i
  have hJn : ∀ n : ℕ, ((JJ B) ^ n).map g = (J ^ n).map i := fun n => by
    rw [hgdef, ← Ideal.map_map, Ideal.map_pow, hJ]
  have hlJB : (l : B.A) ∈ JJ B := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨{ Q := Qo, inl := inl, unit := ?_, I_eq := rfl, univ := ?_, surj := ?_, ker := ?_ }⟩
  · exact hlu ⟨f, hfM⟩
  · intro C gC hu
    have hMu : ∀ s : M, IsUnit (gC.f s) := fun s => locAway_units gC f hu s s.2
    set lift : Localization M →+* C.A := IsLocalization.lift hMu with hliftdef
    have hla : ∀ x, lift (algebraMap B.A (Localization M) x) = gC.f x := IsLocalization.lift_eq hMu
    have hδl : IsδMap DL C.D lift := by
      have e : (W2.map lift).comp (deltaSectionToWittLengthTwo DL) = (deltaSectionToWittLengthTwo C.D).comp lift := by
        apply IsLocalization.ringHom_ext M
        refine RingHom.ext fun x => W2.ext rfl ?_
        change lift (DL.δ (algebraMap B.A (Localization M) x)) =
          C.D.δ (lift (algebraMap B.A (Localization M) x))
        rw [← hDL x, hla, hla, gC.f_δ]
      intro x; exact congrArg W2.snd (RingHom.congr_fun e x)
    have hJle : J.map lift ≤ JJ C := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        map_natCast, hla]
      exact sup_le_sup_left (Ideal.span_le.2 (Set.singleton_subset_iff.2 (gC.f_I d hg.1))) _
    haveI := C.complete
    have hhaus : IsHausdorff (JJ C) C.A := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C.A i J (JJ C) hi C.complete lift hJle
    have hhi : ∀ y, h (i y) = lift y := fun y => RingHom.congr_fun hh y
    have hδh : IsδMap DQ C.D h := by
      refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C.A DQ C.D (J.map i) (JJ C) h ?_ ?_ hhaus ?_
      · rw [← map_natCast i]; exact Ideal.mem_map_of_mem i hlJ
      · rw [Ideal.map_map, hh]; exact hJle
      · intro x n
        obtain ⟨y, hy⟩ := hi.surj x n
        refine ⟨i y, mem_δLocus.2 ?_, by rwa [← Ideal.map_pow]⟩
        rw [← hDQ y, hhi, hhi, hδl]
    have hgC : h.comp g = gC.f := by rw [hgdef, ← RingHom.comp_assoc, hh, IsLocalization.lift_comp]
    have hIC : ∀ x ∈ Ideal.span {g d}, h x ∈ C.I := fun x hx =>
      (Ideal.span_le (I := C.I.comap h)).2 (Set.singleton_subset_iff.2 (by
        show h (g d) ∈ C.I
        rw [← RingHom.comp_apply h g, hgC]; exact gC.f_I d hg.1)) hx
    let H : Hom Qo C :=
      { f := h
        f_δ := hδh
        f_I := hIC
        f_str := fun r x hx => by
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B.str r)
          change Ideal.Quotient.mk _ x = Ideal.quotientMap _ g hIle (B.str r) at hx
          rw [← hb, Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
          rw [← gC.f_str r b hb, Ideal.Quotient.eq, ← hgC, RingHom.comp_apply, ← map_sub]
          exact hIC _ hx }
    refine ⟨H, Hom.ext' hgC, fun y hy => Hom.ext' ?_⟩
    have hy' : y.f.comp g = gC.f := congrArg Hom.f hy
    have hyi : y.f.comp i = h.comp i := IsLocalization.ringHom_ext M (hy'.trans hgC.symm)
    exact GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap _ Q C.A i J (JJ C) hi hhaus y.f h (by rw [hyi, hh]; exact hJle) hyi
  · intro x n
    obtain ⟨y, hy⟩ := hi.surj x n
    obtain ⟨⟨b0, s⟩, hbs⟩ := IsLocalization.mk'_surjective M y
    dsimp only at hbs
    subst hbs
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n s s.2
    refine ⟨k, b0 * t, ?_⟩
    change g f ^ k * x - g (b0 * t) ∈ ((JJ B) ^ n).map g
    have hs : i (IsLocalization.mk' (Localization M) b0 s) * g s = g b0 := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have e : g f ^ k * x - g (b0 * t) = g f ^ k * (x - i (IsLocalization.mk' (Localization M) b0 s)) +
        i (IsLocalization.mk' (Localization M) b0 s) * g (f ^ k - s * t) := by
      rw [map_sub, map_mul, map_mul, map_pow]; linear_combination (g t) * hs
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem g hkt))
    rw [hJn]; exact hy
  · intro b n hb
    change g b ∈ ((JJ B) ^ n).map g at hb
    rw [hJn] at hb
    have h1 := hi.ker _ n hb
    rw [← hJ, ← Ideal.map_pow] at h1
    obtain ⟨⟨⟨j, hj⟩, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff M (Localization M)).1 h1
    rw [← map_mul] at hjs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 hjs
    have hcs : ((c : B.A) * (s : B.A)) * b ∈ JJ B ^ n := by
      have e : ((c : B.A) * (s : B.A)) * b = (c : B.A) * j := by rw [← hc]; ring
      rw [e]; exact Ideal.mul_mem_left _ _ hj
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n ((c : B.A) * (s : B.A)) (M.mul_mem c.2 s.2)
    refine ⟨k, ?_⟩
    have e : f ^ k * b = (f ^ k - ((c : B.A) * (s : B.A)) * t) * b + t * (((c : B.A) * (s : B.A)) * b) := by ring
    rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hkt) (Ideal.mul_mem_left _ _ hcs)

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrismStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_completedLocalizationPrism : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → Nonempty (LocP B f d) := by
  first | exact @GlobalTheory.BSP.GenAway₂ | exact GlobalTheory.BSP.GenAway₂ | (intros; apply GlobalTheory.BSP.GenAway₂ <;> assumption)
end
end
