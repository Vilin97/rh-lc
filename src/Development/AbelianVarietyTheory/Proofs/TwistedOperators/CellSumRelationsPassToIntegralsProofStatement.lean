module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongrStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanishStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongr

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.CellInt

theorem cellBot_iff {G : Type} [Group G] {R K : Subgroup G} {b x : G} :
    (∃ r ∈ R, ∃ a ∈ (⊥ : Subgroup G), ∃ k ∈ K, x = r * a * b * k) ↔ ∃ r ∈ R, ∃ k ∈ K, x = r * b * k := by
  constructor
  · rintro ⟨r, hr, a, ha, k, hk, rfl⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨r, hr, k, hk, by simp⟩
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩

theorem cellWt_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (R K : Subgroup G) (ρ : Measure R) (μ : Measure G) (b : G) :
    cellWt ρ μ K b = (((μ (K : Set G)).toReal / (ρ (cellSet R K b b)).toReal : ℝ) : ℂ) := by
  simp only [cellWt, cellSet, measureReal_def, mul_assoc]

theorem niter_cellSum_at (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (R K : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (hl : l.Nodup)
    (hyp : ∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧
      (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) :
    ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ) (h : ∀ i, H i),
      (∀ β ∈ S, ∀ i, i ∉ l → b β i = h i) →
      (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q →
      (∀ g, (∀ i, i ∉ l → g i = h i) → q g ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) g) →
      NIter ρ μ q l h (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  induction l with
  | nil =>
    intro X S b q h hb hd _ hs
    simp only [NIter, List.map_nil, List.prod_nil, one_mul]
    have hbh : ∀ β ∈ S, b β = h := fun β hβ => funext fun i => hb β hβ i (by simp)
    have hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β' := fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)
    by_cases hq : q h = 0
    · rw [hq]
      exact Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]
    · obtain ⟨β, hβ, -⟩ := hs h (fun _ _ => rfl) hq
      rw [Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]
  | cons i l' ih =>
    intro X S b q h hb hd hq hs
    classical
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩ := hyp i (by simp)
    have hyp' : ∀ j ∈ l', _ := fun j hj => hyp j (List.mem_cons_of_mem _ hj)
    have hq' : BiInv R K l' q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have hne : ∀ j ∈ l', j ≠ i := fun j hj hji => hi (hji ▸ hj)
    set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'
    have qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β) := by
      rintro β g ⟨r, hr, k, hk, rfl⟩
      have h1 := (hq i (by simp) (b β)).1 r hr
      have h2 := (hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk
      simp only [Function.update_self, Function.update_idem] at h2
      rw [h2, h1]
    refine ⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩
    · haveI := hρ; haveI := hρi; haveI := hμ
      have hS := quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0))
        (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ))
        (fun β _ => by
          have := (isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))
          convert this using 1)
      convert hS using 1
      apply Finset.sum_congr rfl
      intro β _
      rw [List.map_cons, List.prod_cons, cellWt_eq (R i)]
      ring
    · intro g
      have key := ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q
        (Function.update h i g) ?base ?dist hq' ?supp
      · convert key using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro β _
        split_ifs with hg
        · have e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β := by
            rw [hWt']
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
          rw [e, qinv β g hg, mul_one]
        · simp
      case base =>
        intro β hβ j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])
      case dist =>
        intro β hβ β' hβ' hc
        obtain ⟨hβS, hgβ⟩ := Finset.mem_filter.1 hβ
        obtain ⟨hβS', hgβ'⟩ := Finset.mem_filter.1 hβ'
        refine hd β hβS β' hβS' ?_
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [cellBot_iff]
          have e1 := dcos_eq_of_mem hgβ
          have e2 := dcos_eq_of_mem hgβ'
          have hm : b β' j ∈ dcos (R j) (K j) (b β' j) := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
          rw [← e2, e1] at hm
          exact hm
        · obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j hj'
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj')] using e
      case supp =>
        intro g' hg' hq0
        have hgi : g' i = g := by simpa using hg' i hi
        obtain ⟨β, hβ, hc⟩ := hs g' (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          have := hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))
          rwa [Function.update_of_ne hji] at this) hq0
        refine ⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩
        · have := hc i (by simp)
          rw [cellBot_iff, hgi] at this
          exact this
        · intro j hj
          obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j (List.mem_cons_of_mem _ hj)
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj)] using e

theorem niter_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  intro ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs
  exact niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq
    (fun g hg => hs g (fun i hi => by simpa using hg i hi))

end GlobalTheory.RowVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  first | exact @GlobalTheory.RowVal.niter_cellSum | exact GlobalTheory.RowVal.niter_cellSum | (intros; apply GlobalTheory.RowVal.niter_cellSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProof

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CellVanishing

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]

def extPt (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) : ∀ i, H i :=
  fun i => if hp : p i then g ⟨i, hp⟩ else h₀ i

lemma extPt_update (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p)
    (x : H j.1) : extPt p h₀ (Function.update g j x) = Function.update (extPt p h₀ g) j.1 x := by
  funext i
  by_cases hi : i = j.1
  · subst hi
    simp [extPt, j.2]
  · have hne : ∀ hp : p i, (⟨i, hp⟩ : Subtype p) ≠ j := fun hp h => hi (by rw [← h])
    rw [Function.update_of_ne hi]
    unfold extPt
    split_ifs with hp
    · rw [Function.update_of_ne (hne hp)]
    · rfl

lemma extPt_at (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p) :
    extPt p h₀ g j.1 = g j := by
  simp [extPt, j.2]

lemma niter_sub (p : ι → Prop) [DecidablePred p] {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i))
    (μ : ∀ i, Measure (H i)) (f : (∀ i, H i) → ℂ) (h₀ : ∀ i, H i) :
    ∀ (l : List (Subtype p)) (g : ∀ j : Subtype p, H j.1) (z : ℂ),
      NIter (R := fun j : Subtype p => R j.1) (fun j => ρ j.1) (fun j => μ j.1) (fun g => f (extPt p h₀ g)) l g z →
      NIter ρ μ f (l.map Subtype.val) (extPt p h₀ g) z := by
  intro l
  induction l with
  | nil =>
    intro g z hz
    simpa [NIter] using hz
  | cons j l ih =>
    intro g z hz
    simp only [List.map_cons, NIter.eq_2] at hz ⊢
    obtain ⟨F, hF, hF'⟩ := hz
    refine ⟨F, hF, fun x => ?_⟩
    rw [← extPt_update]
    exact ih _ _ (hF' x)

end GlobalTheory.CellVanishing

namespace GlobalTheory.RowVal


open GlobalTheory.CellVanishing in
theorem cellVan_holds : CellVan := by
  intro ι _ H _ _ _ _ _ _ _ _ A B R K l hl hS ρ μ ρ' μ' hM X S b w q z α hw hdist hinv hsupp hz hrel
  haveI := Classical.decEq (∀ i, H i)
  have hQ := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι H R ρ μ l 1).1 (Fin 2) Finset.univ α z q (fun n _ => hz n)
  refine GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish ι H A B R K l hl hS ρ μ ρ' μ' hM
    ((S 0).image (b 0) ∪ (S 1).image (b 1)) (fun g => ∑ n ∈ Finset.univ, α n * q n g) _ ?_ ?_ ?_ hQ ?_
  · intro c hc i
    rcases Finset.mem_union.1 hc with hc | hc <;>
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨_, hb, _⟩ := hw _ β hβ
      exact hb i
  · intro i hi h
    constructor
    · intro r hr
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).1 r hr]
    · intro k hk
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).2 k hk]
  · intro h h1 hne
    obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨β, hβ, hc⟩ := hsupp n h h1 (right_ne_zero_of_mul hn)
    refine ⟨b n β, ?_, hc⟩
    fin_cases n
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hβ)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hβ)
  · intro a ha ha1
    let p : ι → Prop := fun i => i ∈ l
    haveI : ∀ j : Subtype p, LocallyCompactSpace (B j.1) := fun j =>
      (hS j.1 j.2).clB.isClosedEmbedding_subtypeVal.locallyCompactSpace

    haveI : ∀ n (β : X n) i, Decidable (b n β i ∈ B i) := fun _ _ _ => Classical.dec _
    let bb : ∀ n, X n → ∀ i, B i := fun n β i => if h : b n β i ∈ B i then ⟨b n β i, h⟩ else 1
    have hbb : ∀ n β (hβ : β ∈ S n), bb n β = fun i => ⟨b n β i, (hw n β hβ).2.1 i⟩ := by
      intro n β hβ
      funext i
      exact dif_pos _
    let qn : Fin 2 → (∀ j : Subtype p, B j.1) → ℂ := fun n g => q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1
    have hg1 : ∀ (g : ∀ j : Subtype p, B j.1) i, i ∉ l → a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1 = 1 := by
      intro g i hi
      simp [extPt, p, hi, ha1 i hi]
    have hmeas : ∀ j ∈ l.attach, IsClosed (((R j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsCompact (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsOpen (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧ (ρ' j.1).IsHaarMeasure ∧
        (ρ' j.1).IsInvInvariant ∧ (μ' j.1).IsHaarMeasure ∧ (μ' j.1).IsMulRightInvariant := by
      intro j _
      have hs := hS j.1 j.2
      obtain ⟨-, -, h3, h4⟩ := hM j.1 j.2
      exact ⟨hs.clR.preimage continuous_subtype_val, hs.clB.isClosedEmbedding_subtypeVal.isCompact_preimage hs.cpt,
        hs.opn, h3, hs.uniRB _ h3, h4, hs.uniB _ h4⟩
    have hcell : ∀ n, NIter (R := fun j : Subtype p => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1) (fun j => μ' j.1)
        (qn n) l.attach 1 (∑ β ∈ S n, w n β * q n (a * b n β)) := by
      intro n
      have hv : ∀ β (hβ : β ∈ S n) i, ((bb n β i : B i) : H i) = b n β i := fun β hβ i => by rw [hbb n β hβ]
      have key := GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1))
        (fun j => (K j.1).subgroupOf (B j.1)) l.attach (List.nodup_attach.2 hl) (fun j => ρ' j.1) (fun j => μ' j.1) hmeas
        (X n) (S n) (fun β j => bb n β j.1) (qn n) (fun β _ j hj => absurd (List.mem_attach l j) hj) ?_ ?_ ?_
      · convert key using 1
        refine Finset.sum_congr rfl fun β hβ => ?_
        obtain ⟨h1, hb, hwβ⟩ := hw n β hβ
        rw [hwβ, hbb n β hβ]
        congr 1
        · exact congrArg List.prod (List.attach_map_val (f := fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩)).symm
        · show q n (a * b n β) = q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (fun j => (⟨b n β j.1, hb j.1⟩ : B j.1)) i).1
          congr 1
          funext i
          by_cases hi : i ∈ l
          · simp [extPt, p, hi]
          · simp [extPt, p, hi, ha1 i hi, h1 i hi]
      · intro β hβ β' hβ' hc
        apply hdist n β hβ β' hβ'
        intro i hi
        obtain ⟨r, hr, a0, ha0, k, hk, e⟩ := hc ⟨i, hi⟩ (List.mem_attach _ _)
        rw [Subgroup.mem_bot] at ha0
        subst ha0
        refine ⟨r.1, Subgroup.mem_subgroupOf.1 hr, 1, (A i).one_mem, k.1, Subgroup.mem_subgroupOf.1 hk, ?_⟩
        have e' := congrArg Subtype.val e
        dsimp only at e'
        simp only [Subgroup.coe_mul, OneMemClass.coe_one, mul_one] at e'
        rw [hv β' hβ', hv β hβ] at e'
        rw [mul_one]
        exact e'
      · intro j _ g
        have hgj : ∀ x : B j.1, (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (Function.update g j x) i).1) =
            Function.update (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1) j.1 (a j.1 * x.1) := by
          intro x
          rw [extPt_update]
          funext i
          by_cases hi : i = j.1
          · subst hi; simp
          · simp [Function.update_of_ne hi]
        have hj1 : (extPt (H := fun i => ↥(B i)) p 1 g j.1) = g j := extPt_at _ _ _ _
        constructor
        · intro r hr
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).1 r.1
            (Subgroup.mem_subgroupOf.1 hr)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (r * g j).1 = r.1 * (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) := by
            rw [hj1, Subgroup.coe_mul, ← mul_assoc, ← mul_assoc, (hS j.1 j.2).comm _ (ha j.1) _ r.2]
          rw [hx]
          exact this
        · intro k hk
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).2 k.1
            (Subgroup.mem_subgroupOf.1 hk)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (g j * k).1 = (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) * k.1 := by
            rw [hj1, Subgroup.coe_mul, mul_assoc]
          rw [hx]
          exact this
      · intro g _ hne
        obtain ⟨β, hβ, hc⟩ := hsupp n _ (hg1 g) hne
        refine ⟨β, hβ, fun j _ => ?_⟩
        obtain ⟨r, hr, a', ha', k, hk, e⟩ := hc j.1 j.2
        have hs := hS j.1 j.2
        have hbB : b n β j.1 ∈ B j.1 := (hw n β hβ).2.1 j.1
        have hkB : k ∈ B j.1 := hs.le hk
        have hgB : (g j).1 ∈ B j.1 := (g j).2
        dsimp only at e
        rw [extPt_at] at e
        obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = (g j).1 * k⁻¹ * (b n β j.1)⁻¹ := ⟨_, rfl⟩
        have hr₀B : r₀ ∈ B j.1 := hr₀ ▸ mul_mem (mul_mem hgB (inv_mem hkB)) (inv_mem hbB)
        have hrr : r = (a j.1 * a'⁻¹) * r₀ := by
          have hc' : a'⁻¹ * r₀ = r₀ * a'⁻¹ := hs.comm _ (inv_mem ha') _ hr₀B
          calc r = (r * a' * b n β j.1 * k) * k⁻¹ * (b n β j.1)⁻¹ * a'⁻¹ := by group
            _ = a j.1 * r₀ * a'⁻¹ := by rw [← e, hr₀]; group
            _ = a j.1 * (a'⁻¹ * r₀) := by rw [hc']; group
            _ = (a j.1 * a'⁻¹) * r₀ := by group
        have hr₀R : r₀ ∈ R j.1 := (hs.split _ (mul_mem (ha j.1) (inv_mem ha')) _ hr₀B (by rw [← hrr]; exact hr)).2
        refine ⟨⟨r₀, hr₀B⟩, Subgroup.mem_subgroupOf.2 hr₀R, 1, Subgroup.one_mem _, ⟨k, hkB⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
        apply Subtype.ext
        show (g j).1 = r₀ * 1 * (bb n β j.1).1 * k
        rw [hv β hβ, hr₀]
        group
    have hlin := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1)
      (fun j => μ' j.1) l.attach 1).1 (Fin 2) Finset.univ α (fun n => ∑ β ∈ S n, w n β * q n (a * b n β)) qn
      (fun n _ => hcell n)
    rw [hrel a ha ha1] at hlin
    have ht := niter_sub p ρ' μ' (fun bb : ∀ i, B i => ∑ n ∈ Finset.univ, α n * q n fun i => a i * (bb i).1) 1 l.attach 1 0 hlin
    have e1 : extPt p (1 : ∀ i, B i) (1 : ∀ j : Subtype p, B j.1) = 1 := by
      funext i; simp [extPt]
    rw [e1, List.attach_map_subtype_val] at ht
    exact ht

end GlobalTheory.RowVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProofStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cellSumRelationsPassToIntegrals_proof : CellVan := by
  first | exact @GlobalTheory.RowVal.cellVan_holds | exact GlobalTheory.RowVal.cellVan_holds | (intros; apply GlobalTheory.RowVal.cellVan_holds <;> assumption)
end
end
