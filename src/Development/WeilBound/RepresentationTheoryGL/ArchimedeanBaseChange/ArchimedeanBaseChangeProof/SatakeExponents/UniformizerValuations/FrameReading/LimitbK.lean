module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PackK

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd



theorem packK (hBO : BlockOperatorsProductAdjoint) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    {Γ : Type} (g : Γ → BGen B) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (ht₀ : t₀.Ok) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (M : ℕ) (f : B.I → H E B.a B.b → ℂ) (c : ℂ) (σ : Γ → ℂ) (hf : ∀ i, Continuous (f i)) (hf0 : f ≠ 0)
    (hLI : LeftInv f) (hW : WL2 B.D M f) (hc : c ≠ 0) (h0 : PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ f = c • f)
    (hAt : ∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ f = σ y • f) :
    ∃ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m =
        (if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0) / c) ∧
      (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m =
        (if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0) / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E B.a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E B.b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ) := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  choose ta hta using hderA
  choose tb htb using hderB
  let ka' : Bool → ℕ → Kers B.Ma := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.a then (ta v s m h.1 h.2).ka v else if m = 0 then (B.a : ℂ) • t₀.ka v else 0
  let kb' : Bool → ℕ → Kers B.Mb := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.b then (tb v s m h.1 h.2).kb v else if m = 0 then (B.b : ℂ) • t₀.kb v else 0
  let ca : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0
  let cb : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0
  have hkerA : ∀ s m v, IsKer B.μa (B.Ma v) [(s, m)] bump (ka' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      rw [e1]; exact (hta v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hka0 v)
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have ha : B.a = 0 := by omega
        rw [e1]; exact isKer_zero_rank ha _ _ _ s m
  have hkerB : ∀ s m v, IsKer B.μb (B.Mb v) [(s, m)] bump (kb' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      rw [e1]; exact (htb v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hkb0 v)
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have hb : B.b = 0 := by omega
        rw [e1]; exact isKer_zero_rank hb _ _ _ s m
  have hderA' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens (Function.update t₀.ka v (ka' s m v)) t₀.kb t₀.ψ) f =
      ca v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      have e2 : ca v s m = σ (der v s m).1 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := hta v s m h.1 h.2
      have hu : Function.update t₀.ka v ((ta v s m h.1 h.2).ka v) = (ta v s m h.1 h.2).ka := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (ta v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        have e2 : ca v s m = (B.a : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have e2 : ca v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero, conv_zeroM, zero_smul]
  have hderB' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens t₀.ka (Function.update t₀.kb v (kb' s m v)) t₀.ψ) f =
      cb v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      have e2 : cb v s m = σ (der v s m).2 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := htb v s m h.1 h.2
      have hu : Function.update t₀.kb v ((tb v s m h.1 h.2).kb v) = (tb v s m h.1 h.2).kb := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (tb v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        have e2 : cb v s m = (B.b : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul_b, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have e2 : cb v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero_b, conv_zeroM, zero_smul]
  have hψl : ∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, t₀.ψ x y ((u₁, u₂) * h) = t₀.ψ x y h := by
    intro x y u₁ hu₁ u₂ hu₂ h
    have hu : ((u₁, u₂) : Hf E B.a B.b) ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) := Subgroup.mem_prod.2 ⟨hu₁, hu₂⟩
    rw [hψ₀, hψ₀]
    simp only [Subgroup.mul_mem_cancel_left _ hu]
  exact hP B.D B.μa B.μb B.ν B.κ t₀.ka t₀.kb t₀.va t₀.vb t₀.T t₀.ψ bump ka' kb' K₁ K₂ M
    f c ca cb B.compat ht₀.ka ht₀.kb ht₀.ψ hbump hka0 hkb0 hkerA hkerB o₁ o₂
    hψl hf hf0 hLI hW hc h0 hderA' hderB'

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbK

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd


theorem perK (hAV : ActVal) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (hjX : ∀ χa' χb', tX.val χa' χb' = t₀.val χa' χb' ^ jX)
    (ha₀ : g a₀ = Sum.inr t₀) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (hcomm : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχn : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  have okOf : ∀ y (t : PT B), g y = Sum.inr t → t.Ok := fun y t hy => by
    have := hok y; rw [hy] at this; exact this
  have ht₀ : t₀.Ok := okOf a₀ t₀ ha₀
  obtain ⟨M, sk, f, hsg, hsX, hk⟩ := hReal E B Γ g a₀ t₀ X tX χ hok htX hXe ha₀ hcomm hXc hXs hχn hχ0
  have hc : ∀ k, sk k (genE g X a₀) ≠ 0 := fun k => (hk k).1
  have hcont : ∀ k i, Continuous (f k i) := fun k => (hk k).2.1
  have hne : ∀ k, f k ≠ 0 := fun k => (hk k).2.2.1
  have heq0 : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = sk k (genE g X a₀) • f k := fun k => (hk k).2.2.2.2.2.1
  have hAt : ∀ k y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) = sk k (genE g X y) • f k := by
    intro k y t hy
    have htok := okOf y t hy
    have e := hCM E B.a B.b B.D B.I t.Φ t₀.Φ (hBO E B t t htok htok).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.1 y t hy, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
        sk k (genE g X a₀) • (sk k (genE g X y) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hAX : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) = sk k (XE g X) • f k := by
    intro k
    have e := hCM E B.a B.b B.D B.I tX.Φ t₀.Φ (hBO E B tX tX htX htX).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.2, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) =
        sk k (genE g X a₀) • (sk k (XE g X) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hPk := fun k => packK hBO B W₁ W₂ K₁ K₂ o₁ o₂ hP g t₀ bump cK der ht₀ hbump hka0 hkb0 hψ₀ hderA hderB M (f k)
    (sk k (genE g X a₀)) (fun y => sk k (genE g X y)) (hcont k) (hne k) (hk k).2.2.2.1 (hk k).2.2.2.2.1 (hc k) (heq0 k)
    (hAt k)
  choose χak χbk hgA hgB hEig hTy hS₁ hS₂ hAu₁ hAu₂ hI₁ hI₂ using hPk
  obtain ⟨hFinA, -⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hrinv : ∀ k, ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x := by
    intro k i u hu x
    exact (hTy k i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hidk : ∀ k, convF B.ν t₀.ψ (f k) = f k := fun k => (hFinA _ (f k) (hrinv k)).1
  have hAVt : ∀ k (t : PT B), t.Ok → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
      t.val (χak k) (χbk k) • convF B.ν t.ψ (f k) := by
    intro k t htok
    exact hAV E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t₀.ka t.ka t₀.kb t.kb t₀.va t.va t₀.vb t.vb t₀.T t.T t₀.ψ t.ψ
      (f k) (χak k) (χbk k) B.compat ht₀.ka ht₀.kb ht₀.ψ ⟨hcont k, _, hc k, heq0 k⟩ ⟨hS₁ k, hS₂ k⟩ (hEig k) htok.ka
      htok.kb htok.ψ
  have hv₀ : ∀ k, t₀.val (χak k) (χbk k) = sk k (genE g X a₀) := by
    intro k
    have e := hAVt k t₀ ht₀
    rw [hidk k, heq0 k] at e
    exact (smul_cancel (hne k) e).symm
  have hFinK : ∀ k y (t : PT B), g y = Sum.inr t → FinType t₀ t →
      convF B.ν t.ψ (f k) = (sk k (genE g X y) / sk k (genE g X a₀)) • f k := by
    intro k y t hy hft
    have htok := okOf y t hy
    have hv : t.val (χak k) (χbk k) = sk k (genE g X a₀) := by
      rw [← hv₀ k]; unfold PT.val; rw [hft.2.2.1, hft.2.2.2.1]
    have e := hAVt k t htok
    rw [hAt k y t hy, hv] at e
    refine smul_right_injective _ (hc k) ?_
    show sk k (genE g X a₀) • _ = sk k (genE g X a₀) • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hc k]
  have hXK : ∀ k, convF B.ν tX.ψ (f k) = (sk k (XE g X) / sk k (genE g X a₀) ^ jX) • f k := by
    intro k
    have e := hAVt k tX htX
    rw [hAX k, hjX, hv₀ k] at e
    have hcj : sk k (genE g X a₀) ^ jX ≠ 0 := pow_ne_zero _ (hc k)
    refine smul_right_injective _ hcj ?_
    show sk k (genE g X a₀) ^ jX • _ = sk k (genE g X a₀) ^ jX • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hcj]
  have hArchK : ∀ k y (t : PT B), g y = Sum.inr t → ArchType t₀ t → t.val (χak k) (χbk k) = sk k (genE g X y) := by
    intro k y t hy hat
    have e := hAVt k t (okOf y t hy)
    rw [hAt k y t hy, show t.ψ = t₀.ψ from hat, hidk k] at e
    exact (smul_cancel (hne k) e).symm
  have hlimA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.a then χ (genE g X (der v s m).1) / χ (genE g X a₀) else if m = 0 then (B.a : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgA k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  have hlimB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.b then χ (genE g X (der v s m).2) / χ (genE g X a₀) else if m = 0 then (B.b : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgB k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  exact ⟨M, sk, f, χak, χbk, hsg, hsX, hlimA, hlimB, fun k => ⟨hc k, hcont k, hne k, (hk k).2.2.2.1,
    (hk k).2.2.2.2.1, hTy k, hS₁ k, hS₂ k, hAu₁ k, hAu₂ k, hI₁ k, hI₂ k, hFinK k, hXK k, hArchK k⟩⟩

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end
