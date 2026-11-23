module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.InfLimit
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionOneMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeFixedSplitPlace
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeVecFst
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.TjZeroAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PackStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.SatakeConjugateInverse
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ValLim

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Imports

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satRead₁ :
    UpperTheory.Zero.ConvolutionTheory.EB.SatRead₁ := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f hf _ hL _ w hw hwZ t ht
  have h := hkAct E a b l₁ l₂ D A S Z L hS hZ f hL w hw hwZ
  obtain ⟨B₁, B₂, h1, h2, h3, h4⟩ := sat2Ex E a b w _ _ (pairRt a b w) f t hf (fun i => (h 0 i).1.1)
    fun p i => ((h p i).1.2).symm.trans (congrFun (ht p) i)
  refine ⟨B₁, B₂, h1, h2, h3, ?_, ?_⟩
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b w _ _ _ (h4 i)).1 φ m e
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b w _ _ _ (h4 i)).2 φ m e
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatRead

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satRead₂ :
    UpperTheory.Zero.ConvolutionTheory.EB.SatRead₂ := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f hf _ hL _ w hw hwZ hs t ht
  have h := hkAct E a b l₁ l₂ D A S Z L hS hZ f hL w hw hwZ
  obtain ⟨B₁, B₂, h1, h2, h3, h4⟩ := sat2Ex E a b w _ _ (pairRtT a b w) f t hf (fun i => ((h 0 i).2 hs).1)
    fun p i => (((h p i).2 hs).2).symm.trans (congrFun (ht p) i)
  have hi : ∀ B, inv (inv B) = B := fun B => by simp [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine ⟨inv B₁, inv B₂, by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using h1, by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using h2, by simpa only [hi] using h3, ?_, ?_⟩
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b _ _ _ _ (sat2Back E a b w _ _ _ hs (h4 i))).1 φ m e
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b _ _ _ _ (sat2Back E a b w _ _ _ hs (h4 i))).2 φ m e
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ReadOne

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.readOne :
    UpperTheory.Zero.ConvolutionTheory.EB.ReadOne := by
  intro E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, hW₁, hW₂, hP⟩ := UpperTheory.Zero.ConvolutionTheory.EB.packStep E a b l₁ l₂
  refine ⟨W₁, W₂, hW₁, hW₂, ?_⟩
  intro D A S Z L hS hZ T e₁ e₂ s f hT hTZ hs hE
  obtain ⟨χa, χb, hχa, hχb, hL, hSm, hs₁, hs₂, hv⟩ := hP D A S Z L hS hZ T e₁ e₂ s f hs hE
  obtain ⟨-, hPl, -, hSec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E

  obtain ⟨i, x, hx⟩ : ∃ i x, f i x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hE.ne (funext fun i => funext fun x => h i x)
  obtain ⟨φ₁, hφ₁⟩ := hSm.1 i x.2
  obtain ⟨φ₂, hφ₂⟩ := hSm.2 i x.1
  have hm₁ : φ₁ ∈ slices₁ f := ⟨i, x.2, hφ₁⟩
  have hm₂ : φ₂ ∈ slices₂ f := ⟨i, x.1, hφ₂⟩
  have hn₁ : φ₁ ≠ 0 := by
    rintro rfl
    exact hx (by simpa using (congrFun hφ₁ x.1).symm)
  have hn₂ : φ₂ ≠ 0 := by
    rintro rfl
    exact hx (by simpa using (congrFun hφ₂ x.2).symm)

  let t₁ : Pl E → Fin (a + 1) × Fin (b + 1) → ℂ := fun w p =>
    if h : w ∈ S ∧ w ∉ Z then s (.inr (.inr (.inl (⟨w, h⟩, p, false)))) / s (.inl ()) else 0
  let t₂ : Pl E → Fin (a + 1) × Fin (b + 1) → ℂ := fun w p =>
    if h : w ∈ S ∧ w ∉ Z then s (.inr (.inr (.inl (⟨w, h⟩, p, true)))) / s (.inl ()) else 0
  have ht₁ : ∀ w, w ∈ S → w ∉ Z → ∀ p, convF A.ν (A.hk1 S L w p false) f = t₁ w p • f := by
    intro w hw hwZ p
    have h : t₁ w p = s (.inr (.inr (.inl (⟨w, hw, hwZ⟩, p, false)))) / s (.inl ()) := dif_pos ⟨hw, hwZ⟩
    rw [h]
    exact hv (.inl (⟨w, hw, hwZ⟩, p, false))
  have ht₂ : ∀ w, w ∈ S → w ∉ Z → ∀ p, convF A.ν (A.hk1 S L w p true) f = t₂ w p • f := by
    intro w hw hwZ p
    have h : t₂ w p = s (.inr (.inr (.inl (⟨w, hw, hwZ⟩, p, true)))) / s (.inl ()) := dif_pos ⟨hw, hwZ⟩
    rw [h]
    exact hv (.inl (⟨w, hw, hwZ⟩, p, true))

  have key : ∀ w : Pl E, ∃ B₁ B₂ : Multiset ℂˣ, Off Z w → B₁.card = a ∧ B₂.card = b ∧
      IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ₁ B₁ ∧ IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ₂ B₂ ∧
      (w ∈ S → ∀ p, t₁ w p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧
      (w ∉ S → ∀ p, t₂ (cPl w) p = satEig (qV E (cPl w)) a (inv B₁) p.1 * satEig (qV E (cPl w)) b (inv B₂) p.2) := by
    intro w
    by_cases hO : Off Z w
    · by_cases hw : w ∈ S
      · obtain ⟨B₁, B₂, c₁, c₂, he, h₁, h₂⟩ := UpperTheory.Zero.ConvolutionTheory.EB.satRead₁ E a b l₁ l₂ D A S Z L hS hZ f hE.ne hE.cont hL hSm
          w hw hO.1 (t₁ w) (ht₁ w hw hO.1)
        exact ⟨B₁, B₂, fun _ => ⟨c₁, c₂, h₁ φ₁ hm₁ hn₁, h₂ φ₂ hm₂ hn₂, fun _ => he, fun h => absurd hw h⟩⟩
      · have hu : cPl w ∈ S := ((hSec S hS w).1).resolve_left hw
        have hsp : IsSplitAt (cPl w) := by
          rw [(hPl (cPl w)).2, (hPl w).1]
          intro h
          exact hw (h ▸ hu)
        obtain ⟨u, rfl⟩ : ∃ u, w = cPl u := ⟨cPl w, ((hPl w).1).symm⟩
        rw [(hPl u).1] at hu hsp
        obtain ⟨B₁, B₂, c₁, c₂, he, h₁, h₂⟩ := UpperTheory.Zero.ConvolutionTheory.EB.satRead₂ E a b l₁ l₂ D A S Z L hS hZ f hE.ne hE.cont hL hSm
          u hu (by simpa [(hPl u).1] using hO.2) hsp (t₂ u) (ht₂ u hu (by simpa [(hPl u).1] using hO.2))
        refine ⟨B₁, B₂, fun _ => ⟨?_, ?_, h₁ φ₁ hm₁ hn₁, h₂ φ₂ hm₂ hn₂, fun h => absurd h hw, fun _ => ?_⟩⟩
        · exact c₁
        · exact c₂
        · simpa only [(hPl u).1] using he
    · exact ⟨0, 0, fun h => absurd h hO⟩
  choose B₁ B₂ hB using key
  refine ⟨χa, χb, φ₁, φ₂, B₁, B₂, hχa, hχb, hm₁, hn₁, (hs₁ φ₁ hm₁).1, (hs₁ φ₁ hm₁).2.1, (hs₁ φ₁ hm₁).2.2, hn₂,
    (hs₂ φ₂ hm₂).1, (hs₂ φ₂ hm₂).2.1, (hs₂ φ₂ hm₂).2.2, ?_, ?_⟩
  · intro w hO
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hB w hO
    exact ⟨h1, h2, h3, h4⟩
  ·
    have hTS : ∀ w ∈ T, w ∈ S ∧ w ∉ Z := fun w hw => ⟨hT.1 w hw, Finset.disjoint_left.mp hTZ hw⟩
    have hTEv : TEv S T e₂ := ⟨hT.1, fun w hw hn x => by rw [hT.2 w hw hn]; rfl⟩
    have h1 := UpperTheory.Zero.ConvolutionTheory.EB.hkVal E a b l₁ l₂ D A S Z L hS hZ f t₁ t₂ T e₁ e₂ hTEv hTZ hE.cont hL
      (fun w hw p => ⟨ht₁ w (hTS w hw).1 (hTS w hw).2 p, fun _ => ht₂ w (hTS w hw).1 (hTS w hw).2 p⟩)
    have h2 : convF A.ν (A.hk S L T e₁ e₂) f = (s (.inr (.inr (.inr ()))) / s (.inl ())) • f := hv (.inr ())
    have h3 : s (.inr (.inr (.inr ()))) / s (.inl ()) = ∏ w ∈ T, (e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w) := by
      have h4 := congrFun (congrFun (h2.symm.trans h1) i) x
      simp only [Pi.smul_apply, smul_eq_mul] at h4
      exact mul_right_cancel₀ hx h4
    rw [h3]
    refine Finset.prod_congr rfl fun w hw => ?_
    obtain ⟨hwS, hwZ⟩ := hTS w hw
    have hOff : Off Z w := by
      refine ⟨hwZ, fun hc => hwZ ?_⟩
      have hcs := hZ _ hc
      have : cPl w = w := (hSec S hS w).2 hwS hcs.1
      exact this ▸ hc
    have hA : (e₁ w).ev (t₁ w) = ev2 a b w (e₁ w) (B₁ w) (B₂ w) := by
      have := (hB w hOff).2.2.2.2.1 hwS
      unfold ev2
      congr 1
      exact funext this
    have hC : (e₂ w).ev (t₂ w) = ev2 a b w (e₂ w) (inv (B₁ (cPl w))) (inv (B₂ (cPl w))) := by
      by_cases hsp : IsSplitAt w
      · have hne : cPl w ≠ w := ((hPl w).2).1 hsp
        have hnS : cPl w ∉ S := fun h => hne ((hSec S hS w).2 hwS h)
        have hOc : Off Z (cPl w) := by
          refine ⟨fun hc => hnS (hZ _ hc).1, ?_⟩
          rw [(hPl w).1]
          exact hwZ
        have := (hB (cPl w) hOc).2.2.2.2.2 hnS
        simp only [(hPl w).1] at this
        unfold ev2
        congr 1
        exact funext this
      · rw [hT.2 w hw hsp]
        rfl
    rw [hA, hC]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem bad_finite {E : Type} [Field E] [NumberField E] [IsCMField E] (Z : Finset (Pl E)) :
    {w : Pl E | ¬ Off Z w}.Finite := by
  obtain ⟨-, hcp, -, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hinj : Function.Injective (cPl : Pl E → Pl E) := fun x y h => by
    rw [← (hcp x).1, ← (hcp y).1, h]
  refine (Z.finite_toSet.union (Z.finite_toSet.preimage hinj.injOn)).subset fun w hw => ?_
  by_contra hc
  exact hw ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩

private theorem off_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Set (Pl E)}
    (hS : IsSection S) {Z T : Finset (Pl E)} (hZ : SplitIn S Z) (hT : ∀ w ∈ T, w ∈ S)
    (hd : Disjoint T Z) (w : Pl E) (hw : w ∈ T ∨ cPl w ∈ T) : Off Z w := by
  obtain ⟨-, hcp, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have key : ∀ u ∈ T, Off Z u := fun u hu => by
    refine ⟨Finset.disjoint_left.1 hd hu, fun hc => ?_⟩
    have e := (hsec S hS u).2 (hT u hu) (hZ _ hc).1
    rw [e] at hc
    exact Finset.disjoint_left.1 hd hu hc
  rcases hw with h | h
  · exact key w h
  · have h' := key _ h
    rw [Off, (hcp w).1] at h'
    exact ⟨h'.2, h'.1⟩

theorem rRead : RRead := by
  intro P hP E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, hW₁, hW₂, hR⟩ := readOne E a b l₁ l₂
  refine ⟨W₁, hW₁, fun D A S Z L hS hZ X hX hXc => ?_⟩
  obtain ⟨o₁, -, k₁⟩ := kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩)
    (fun w hw => (L.off w hw).1)
  obtain ⟨o₂, -, k₂⟩ := kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩)
    (fun w hw => (L.off w hw).2)
  have off_of : ∀ {w : Pl E}, w ∉ {w : Pl E | ¬ Off Z w} → Off Z w :=
    fun h => Classical.byContradiction fun hn => h hn
  have of_off : ∀ {w : Pl E}, Off Z w → w ∉ {w : Pl E | ¬ Off Z w} := fun h h' => h' h
  obtain ⟨J₁, hJ₁, D₁, C₁, a₁, p₁, r₁⟩ := hP E a (Kg S L.L₁) W₁ {w | ¬ Off Z w} (mW l₁) X o₁ hW₁
    (bad_finite Z) (fun w hw k hk => k₁ w (off_of hw) k hk) hX hXc
  obtain ⟨J₂, hJ₂, D₂, C₂, a₂, p₂, r₂⟩ := hP E b (Kg S L.L₂) W₂ {w | ¬ Off Z w} (mW l₂) ∅ o₂ hW₂
    (bad_finite Z) (fun w hw k hk => k₂ w (off_of hw) k hk) Set.subsingleton_empty
    (fun π h => absurd h (Set.notMem_empty π))
  refine ⟨J₁ × J₂, inferInstance, fun j => D₁ j.1, fun j => D₂ j.2, fun j => C₁ j.1, fun j => C₂ j.2,
    fun j => ⟨(a₁ j.1).1, fun w hw => ⟨(a₁ j.1).2 w (of_off hw), (a₂ j.2).2 w (of_off hw)⟩⟩,
    fun j => ⟨p₁ j.1, p₂ j.2⟩, ?_⟩
  intro T e₁ e₂ g s hT hd hSees harch hReal
  obtain ⟨sk, f, hsk, hf⟩ := hReal
  have hr := fun k => hR D A S Z L hS hZ T e₁ e₂ (sk k) (f k) hT hd (hf k).1 (hf k).2.1
  choose χa χb φ₁ φ₂ B₁ B₂ ha hb hsl n₁ u₁ t₁ c₁ n₂ u₂ t₂ c₂ hoff hv using hr
  obtain ⟨h0, ca, cb⟩ := infLimit E a b l₁ l₂ D A S Z L T e₁ e₂ s sk χa χb harch hsk ha hb
  obtain ⟨j₁, s₁, hs₁, q₁⟩ := r₁ φ₁ (fun k => mOf (χa k)) B₁
    (fun k => ⟨n₁ k, u₁ k, t₁ k, c₁ k, fun w hw => (hoff k w (off_of hw)).2.2.1, fun π hπ ψ hψ z => by
      obtain ⟨i, m₂, hi⟩ := hsl k
      exact hSees (f k) (hf k).2.2 i m₂ (φ₁ k) hi (n₁ k) (t₁ k) π hπ ψ hψ z⟩) ca
  obtain ⟨j₂, s₂, hs₂, q₂⟩ := r₂ (fun k => φ₂ (s₁ k)) (fun k => mOf (χb (s₁ k))) (fun k => B₂ (s₁ k))
    (fun k => ⟨n₂ _, u₂ _, t₂ _, c₂ _, fun w hw => (hoff _ w (off_of hw)).2.2.2,
      fun π hπ => absurd hπ (Set.notMem_empty π)⟩)
    (fun τ ε hε => hs₁.tendsto_atTop.eventually (cb τ ε hε))
  refine ⟨(j₁, j₂), ?_⟩
  have hut : Tendsto (fun k => s₁ (s₂ k)) atTop atTop := (hs₁.comp hs₂).tendsto_atTop
  have lim₁ : Tendsto (fun k => val T e₁ e₂ (B₁ (s₁ (s₂ k))) (B₂ (s₁ (s₂ k)))) atTop
      (𝓝 (val T e₁ e₂ (C₁ j₁) (C₂ j₂))) := by
    refine valLim E a b T e₁ e₂ _ _ _ _ fun w hw => ?_
    have hw' : Off Z w := off_of_mem hS hZ hT.1 hd w hw
    exact ⟨satCard E a (D₁ j₁) w _ ((a₁ j₁).2 w (of_off hw')),
      satCard E b (D₂ j₂) w _ ((a₂ j₂).2 w (of_off hw')),
      fun k => ⟨(hoff _ w hw').1, (hoff _ w hw').2.1⟩,
      fun i => (q₁ w (of_off hw') i).comp hs₂.tendsto_atTop,
      fun i => q₂ w (of_off hw') i⟩
  have hne : s (.inl ()) ≠ 0 := by rw [h0]; exact one_ne_zero
  have lim₂ := ((hsk (.inr (.inr (.inr ())))).div (hsk (.inl ())) hne).comp hut
  rw [h0, div_one] at lim₂
  exact tendsto_nhds_unique (lim₂.congr fun k => hv _) lim₁

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
end
