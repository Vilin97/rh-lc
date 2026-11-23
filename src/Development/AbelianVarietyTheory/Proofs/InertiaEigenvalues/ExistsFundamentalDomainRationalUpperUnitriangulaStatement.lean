module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.Adele.Discrete
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import GroundTheory.GlobalFields.Adele.Compact

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundame

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

noncomputable section

namespace GlobalTheory.CellDec.RatUnip

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem row_mul_split (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (r : Fin n → E) (j : Fin n) :
    ∑ k, algebraMap E (Ad E) (r k) * w k j =
      (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) + algebraMap E (Ad E) (r j) := by
  have key : ∀ k, algebraMap E (Ad E) (r k) * w k j =
      (if k < j then algebraMap E (Ad E) (r k) * w k j else 0) +
        (if j = k then algebraMap E (Ad E) (r k) else 0) := by
    intro k
    rcases lt_trichotomy k j with h | rfl | h
    · simp [h, h.ne']
    · simp [hd]
    · simp [not_lt.2 h.le, h.ne, hl k j h]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem row_unique (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) (r r' : Fin n → E)
    (h0 : ∀ k, k < i → r k = 0) (h0' : ∀ k, k < i → r' k = 0) (h1 : r i = 1) (h1' : r' i = 1)
    (hF : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E)
    (hF' : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r' k) * w k j ∈ GroundTheory.Global.fundamentalSet E) :
    r = r' := by
  suffices h : ∀ m : ℕ, ∀ j : Fin n, j.val < m → r j = r' j from
    funext fun j => h _ j j.val.lt_succ_self
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact ih j hj
    rcases lt_trichotomy j i with h | rfl | h
    · rw [h0 j h, h0' j h]
    · rw [h1, h1']
    · have hs : (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) =
          ∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [ih k (by have := Fin.lt_def.1 hk; omega)]
        · rfl
      have a := hF j h
      have b := hF' j h
      rw [row_mul_split w hl hd] at a b
      rw [hs] at a
      obtain ⟨c, -, hc⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0)
      have e1 := hc (-r j) (by simpa using a)
      have e2 := hc (-r' j) (by simpa using b)
      exact neg_injective (e1.trans e2.symm)

theorem row_exists (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) :
    ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E := by
  suffices h : ∀ m : ℕ, ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j : Fin n, i < j → j.val < m →
        ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E by
    obtain ⟨r, h0, h1, h2⟩ := h n
    exact ⟨r, h0, h1, fun j hj => h2 j hj j.isLt⟩
  intro m
  induction m with
  | zero =>
    exact ⟨Pi.single i 1, fun k hk => by simp [Pi.single_apply, hk.ne], by simp,
      fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨r, h0, h1, h2⟩ := ih
    by_cases hm : ∃ jm : Fin n, jm.val = m ∧ i < jm
    · obtain ⟨jm, hjm, hijm⟩ := hm
      obtain ⟨c, hc, -⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, algebraMap E (Ad E) (r k) * w k jm)
      refine ⟨r - Pi.single jm c, fun k hk => ?_, ?_, fun j hij hj => ?_⟩
      · simp [h0 k hk, Pi.single_apply, (hk.trans hijm).ne]
      · simp [h1, Pi.single_apply, hijm.ne]
      · have hsum : ∑ k, algebraMap E (Ad E) ((r - Pi.single jm c : Fin n → E) k) * w k j =
            ∑ k, algebraMap E (Ad E) (r k) * w k j - algebraMap E (Ad E) c * w jm j := by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          congr 1
          rw [Finset.sum_eq_single jm]
          · simp
          · intro k _ hk; simp [Pi.single_apply, hk]
          · simp
        rw [hsum]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · have hlt : j < jm := by rw [Fin.lt_def]; omega
          rw [hl jm j hlt, mul_zero, sub_zero]
          exact h2 j hij hj
        · have : j = jm := Fin.ext (hj.trans hjm.symm)
          subst this
          rw [hd, mul_one]; exact hc
    · refine ⟨r, h0, h1, fun j hij hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact h2 j hij hj
      · exact absurd ⟨j, hj, hij⟩ hm

end GlobalTheory.CellDec.RatUnip

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.RatUnip

theorem existsUnique_ratUnip_mul_mem_fundamentalSet (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n)
    (hu : u ∈ GlobalTheory.CellDec.NA E n) :
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hent : ∀ (γ : GL (Fin n) E) (i j : Fin n),
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
        ∑ k, algebraMap E (Ad E) ((γ : Matrix (Fin n) (Fin n) E) i k) * (u : Matrix (Fin n) (Fin n) (Ad E)) k j := by
    intro γ i j
    simp [ratGL, Matrix.mul_apply]
  choose r h0 h1 hF using row_exists (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => r i k
  have hM : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular (show M.BlockTriangular id from fun i j hij => h0 i j hij)]
    simp [M, h1]
  refine ⟨Matrix.nonsingInvUnit M hM,
    ⟨(GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => h0 i j hij, fun i => h1 i⟩, fun i j hij => ?_⟩, ?_⟩
  · rw [hent]; exact hF i j hij
  · rintro γ ⟨hγ, hγF⟩
    obtain ⟨gl, gd⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
    apply Units.ext
    ext i j
    have := row_unique (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd i
      (fun k => (γ : Matrix (Fin n) (Fin n) E) i k) (r i) (fun k hk => gl i k hk) (h0 i) (gd i) (h1 i)
      (fun j hij => by rw [← hent]; exact hγF i j hij) (hF i)
    exact congrFun this j

end GlobalTheory.CellDec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundameStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  first | exact @GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | exact GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | (intros; apply GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactAdelicUnitriangularEntriesMemCompact

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CellDec

theorem isCompact_unip_entries_mem :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  intro E _ _ n C hC
  classical
  let S : Fin n → Fin n → Set (Ad E) := fun i j => if j < i then {0} else if i = j then {1} else C
  let P : Set (Matrix (Fin n) (Fin n) (Ad E)) := Set.univ.pi fun i => Set.univ.pi (S i)
  have hP : IsCompact P := by
    refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
    simp only [S]
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_singleton
    · exact hC
  have memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔
      (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C := by
    intro M
    change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _
    simp only [S]
    constructor
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩
      · have := h i trivial j trivial; rw [if_pos hji] at this; exact this
      · have := h i trivial i trivial; rw [if_neg (lt_irrefl i), if_pos rfl] at this; exact this
      · have := h i trivial j trivial; rw [if_neg (not_lt.2 hij.le), if_neg hij.ne] at this; exact this
    · rintro ⟨h0, h1, hc⟩ i - j -
      split_ifs with hji hij
      · exact h0 i j hji
      · subst hij; exact h1 i
      · exact hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)
  have hdet : ∀ M ∈ P, M.det = 1 := by
    intro M hM
    obtain ⟨h0, h1, -⟩ := (memP M).1 hM
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]
    simp [h1]
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) ''
      {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} =
      (fun M => (M, MulOpposite.op M.adjugate)) '' P := by
    ext x
    constructor
    · rintro ⟨g, ⟨hN, hc⟩, rfl⟩
      obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN
      have hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P := (memP _).2 ⟨h0, h1, hc⟩
      refine ⟨g, hgP, ?_⟩
      have hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
        calc (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate
            = (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * g) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate := by
              rw [Units.inv_mul, Matrix.one_mul]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by
              rw [Matrix.mul_assoc]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
              rw [Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]
      simp only [Units.embedProduct_apply, hadj]
    · rintro ⟨M, hM, rfl⟩
      have hd := hdet M hM
      let g : GA E n := ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul],
        by rw [Matrix.adjugate_mul, hd, one_smul]⟩
      obtain ⟨h0, h1, hc⟩ := (memP M).1 hM
      refine ⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩
      rfl
  rw [key]
  exact hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))

end GlobalTheory.CellDec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactAdelicUnitriangularEntriesMemCompactStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

theorem _root_.GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  first | exact @GlobalTheory.CellDec.isCompact_unip_entries_mem | exact GlobalTheory.CellDec.isCompact_unip_entries_mem | (intros; apply GlobalTheory.CellDec.isCompact_unip_entries_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangula

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

def unipFund (E : Type) [Field E] [NumberField E] (n : ℕ) : Set (NA E n) :=
  {u | ∀ i j : Fin n, i < j → ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E}

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ratGL_mem_NA {γ : GL (Fin n) E} (hγ : γ ∈ GlobalTheory.SmGL.unipB E (Fin n)) : ratGL E n γ ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [ratGL, h1 i j hij]
  · simp [ratGL, h2 i]

theorem exists_fundamentalDomain_NE (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (NA E n)) [ν.IsHaarMeasure] : ∃ D : Set (NA E n),
    IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  classical
  have hfd : IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) (unipFund E n) ν := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · refine MeasurableSet.nullMeasurableSet ?_
      have : unipFund E n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
          (fun u : NA E n => ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) ⁻¹'
            GroundTheory.Global.fundamentalSet E := by
        ext u; simp [unipFund]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      refine (Continuous.measurable ?_) (GroundTheory.Global.measurableSet_fundamentalSet E)
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
    · intro x
      obtain ⟨γ, ⟨hγ, hγD⟩, huniq⟩ := GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet E n (x : GA E n) x.2
      refine ⟨⟨⟨ratGL E n γ, ratGL_mem_NA hγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)⟩,
        fun i j hij => hγD i j hij, ?_⟩
      intro g hg
      obtain ⟨γ', hγ', hγ'g⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
      have he : γ' = γ := huniq γ' ⟨hγ', fun i j hij => by
        have := hg i j hij
        rw [hγ'g]; exact this⟩
      apply Subtype.ext; apply Subtype.ext
      change ((g : NA E n) : GA E n) = ratGL E n γ
      rw [← hγ'g, he]
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hG : Countable ((NE E n).subgroupOf (NA E n)) := by
    have h : ∀ g : (NE E n).subgroupOf (NA E n), ∃ γ : GL (Fin n) E, ratGL E n γ = ((g : NA E n) : GA E n) :=
      fun g => by
        obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
        exact ⟨γ, hγ⟩
    choose f hf using h
    have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    have : Countable (GL (Fin n) E) :=
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E))
        fun a b h => Units.ext h
    exact Function.Injective.countable (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (by rw [← hf a, ← hf b, hab]))
  have hinv : SMulInvariantMeasure ((NE E n).subgroupOf (NA E n)) (NA E n) ν :=
    ⟨fun g s _ => by
      have : (fun x : NA E n => g • x) = fun x => (g : NA E n) * x := rfl
      show ν ((fun x => g • x) ⁻¹' s) = ν s
      rw [this]; exact measure_preimage_mul ν (g : NA E n) s⟩
  refine ⟨unipFund E n, hfd, pos_iff_ne_zero.2 (hfd.measure_ne_zero (NeZero.ne ν)), ?_⟩
  set C : Set (Ad E) := closure (GroundTheory.Global.fundamentalSetInfinite E) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E)) with hCdef
  have hC : IsCompact C := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite E).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles E)
  set K : Set (GA E n) := {g : GA E n | g ∈ NA E n ∧ ∀ i j : Fin n, i < j →
    (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} with hKdef
  have hK : IsCompact ((Subtype.val : NA E n → GA E n) ⁻¹' K) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    change IsCompact (K ∩ (NA E n : Set (GA E n)))
    rw [Set.inter_eq_left.2 (fun g (hg : g ∈ K) => hg.1)]
    exact GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact E n C hC
  refine (measure_mono fun u hu => ?_).trans_lt hK.measure_lt_top
  refine ⟨u.2, fun i j hij => ?_⟩
  have h := hu i j hij
  exact ⟨subset_closure h.1, h.2⟩

end GlobalTheory.CellDec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangulaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ∃ D : Set (GlobalTheory.CellDec.NA E n),
    IsFundamentalDomain ((GlobalTheory.CellDec.NE E n).subgroupOf (GlobalTheory.CellDec.NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  first | exact @GlobalTheory.CellDec.exists_fundamentalDomain_NE | exact GlobalTheory.CellDec.exists_fundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_fundamentalDomain_NE <;> assumption)
end
end
