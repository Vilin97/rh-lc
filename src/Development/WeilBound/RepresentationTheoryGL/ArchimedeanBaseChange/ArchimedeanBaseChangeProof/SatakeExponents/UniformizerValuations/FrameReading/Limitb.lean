module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.FinSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.ConvEqOfIsROp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimPhi
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbConv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbK

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg

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

theorem bsG' (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem bsF' (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG' bsF'

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Real

variable {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) (t₀ : PT B)

def phiG (x : ChAlg g X) : Matrix B.I B.I (H E B.a B.b → ℂ) :=
  if h : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) then
    h.choose
  else 0

theorem mul_facts (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (t : PT B) (ht : t.Ok) (ht₀ : t₀.Ok) :
    IsTestM (mulM B.D.μ t.Φ t₀.Φ) ∧ IsROp B.D (mulM B.D.μ t.Φ t₀.Φ) (t.op * t₀.op) := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := hTM E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t₀.ka t.kb t₀.kb t.va t₀.va t.vb t₀.vb t.T t₀.T t.ψ t₀.ψ
      B.compat ht.ka ht.kb ht₀.ka ht₀.kb ht.ψ ht₀.ψ
  have hΦ : mulM B.D.μ t.Φ t₀.Φ = (t.mul t₀).Φ := hm.2
  obtain ⟨-, -, hok, hop, -⟩ := hBO E B t t₀ ht ht₀
  have h2 := hBO E B (t.mul t₀) (t.mul t₀) hok hok
  rw [hΦ, ← hop]
  exact ⟨h2.1, h2.2.1⟩

theorem ok_of_inr {t : PT B} {y : Γ} (hok : ∀ x, (g x).Ok) (hy : g y = Sum.inr t) : t.Ok := by
  have := hok y
  rw [hy] at this
  exact this


theorem realise_commuting_family (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords)
    [Countable Γ] (a₀ : Γ) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (ha₀ : g a₀ = Sum.inr t₀)
    (hc : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχ : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
      (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
      Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
      ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
        (∀ y (t : PT B), g y = Sum.inr t →
          PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) = (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k := by
  have ht₀ : t₀.Ok := ok_of_inr g hok ha₀
  have ea : ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t₀.op := by
    show (g a₀).op = _
    rw [ha₀]
    rfl
  have hspec : ∀ x : ChAlg g X, IsTestM (phiG g X t₀ x) ∧ IsROp B.D (phiG g X t₀ x) ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) :=
    fun x => by
      have h := phiEx hBO hBW hBS hAW g X tX t₀ hok htX hXe ht₀ x
      unfold phiG
      rw [dite_eq_left h]
      exact h.choose_spec
  have hcomm : ∀ x y : ChAlg g X, x * y = y * x := by
    apply isMulCommutative_iff.mp
    apply StarAlgebra.isMulCommutative_adjoin ℂ
    · rintro u (⟨x, rfl⟩ | rfl)
      · exact ⟨(hc x x).2.symm.eq⟩
      · exact ⟨by rw [hXs.star_eq]; rfl⟩
    · rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hc x y).1
      · exact ((hXc x).1).symm
      · exact (hXc y).1
      · rfl
    · rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hc x y).2
      · rw [hXs.star_eq]; exact ((hXc x).1).symm
      · exact (hXc y).2
      · rw [hXs.star_eq]; rfl
  letI : CommRing (ChAlg g X) :=
    { (inferInstance : Ring (ChAlg g X)) with mul_comm := hcomm }
  have hCc : ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)).Countable :=
    ((Set.countable_singleton _).union (Set.countable_range _)).union (Set.countable_singleton _)
  obtain ⟨M, s, f, hlim, hk⟩ := hE2 E B.a B.b B.D B.I B.Hb (ContinuousLinearMap.id ℂ B.Hb) (fun v => rfl) (ChAlg g X)
    (StarSubalgebra.subtype _) χ (genE g X a₀) ({1} ∪ Set.range (genE g X) ∪ {XE g X}) (phiG g X t₀) hχ hχ0 hCc
    (Or.inl (Or.inl rfl)) (fun x => (hspec x).1) (fun x => ⟨_, (hspec x).2, fun v => by
      change ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) v =
        ((x : B.Hb →L[ℂ] B.Hb) * ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb)) v
      rw [ea], fun u hu => by
      have hu0 : u = 0 := inner_self_eq_zero.1 (hu u)
      rw [hu0, map_zero]⟩)
  refine ⟨M, fun k x => s k x, f, fun y => hlim _ (Or.inl (Or.inr ⟨y, rfl⟩)), hlim _ (Or.inr rfl), fun k => ?_⟩
  obtain ⟨h0, hcont, hne, hL, hW, hconv⟩ := hk k
  have key : ∀ x ∈ ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)), ∀ Ψ, IsTestM Ψ →
      IsROp B.D Ψ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) →
      PositivityTheory.Rg.BcB.E.conv B.D.μ Ψ (f k) = s k (x * genE g X a₀) • f k := fun x hx Ψ h1 h2 =>
    (PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D h1 (hspec x).1 h2 (hspec x).2 hcont hL).trans (hconv x hx)
  refine ⟨h0, hcont, hne, hL, hW, ?_, fun y t hy => ?_, ?_⟩
  · have h0' := hBO E B t₀ t₀ ht₀ ht₀
    have h := key 1 (Or.inl (Or.inl rfl)) t₀.Φ h0'.1 (by
      show IsROp B.D t₀.Φ (1 * t₀.op)
      rw [one_mul]
      exact h0'.2.1)
    rw [one_mul] at h
    exact h
  · have ht := ok_of_inr g hok hy
    have hm := mul_facts t₀ hTM hBO t ht ht₀
    have e : ((genE g X y : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t.op := by
      show (g y).op = _
      rw [hy]
      rfl
    have h := key (genE g X y) (Or.inl (Or.inr ⟨y, rfl⟩)) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h
  · have hm := mul_facts t₀ hTM hBO tX htX ht₀
    have e : ((XE g X : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = tX.op := hXe
    have h := key (XE g X) (Or.inr rfl) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h

end Real

theorem realise (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords) :
    RealiseSt := by
  intro E _ _ _ B Γ _ g a₀ t₀ X tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0
  exact realise_commuting_family g X t₀ hE2 hTM hBO hBW hBS hAW a₀ tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbC

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



theorem hecke_setup (hFH : FinHecke) (hBO : BlockOperatorsProductAdjoint) (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (B : Block E) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (t₀ : PT B) (h₀ : t₀.Ok) (cK : ℂ)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (Λ : Type) (tΛ : Λ → PT B) (hok : ∀ l, (tΛ l).Ok) (f : ℕ → B.I → H E B.a B.b → ℂ) (hf0 : ∀ k, f k ≠ 0)
    (hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x)
    (r : Λ → ℕ → ℂ) (r₀ : Λ → ℂ) (hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k)
    (hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l))) :
    ∃ (hm : Λ → HeckeM E B.a B.b B.I) (lam : ℕ → HeckeM E B.a B.b B.I → ℂ) (lam₀ : HeckeM E B.a B.b B.I → ℂ),
      (∀ k, ∀ h ∈ Set.range hm, heckeAct h (f k) = lam k h • f k) ∧
      (∀ h ∈ Set.range hm, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) ∧
      ∀ l (F : B.I → H E B.a B.b → ℂ),
        (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
        heckeAct (hm l) F = convF B.ν (tΛ l).ψ F ∧ lam₀ (hm l) = r₀ l := by
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hFinA, hFinB⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hUo : IsOpen (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact o₁.prod o₂
  have hUc : IsCompact (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact c₁.prod c₂
  have hψF : ∀ l, IsFinM (mulF B.ν (tΛ l).ψ t₀.ψ) := fun l => (hBO E B (tΛ l) t₀ (hok l) h₀).2.2.1.ψ
  have hex := fun l => hFH E B.a B.b B.ν (IxA B.Ma × IxA B.Mb) B.κ (mulF B.ν (tΛ l).ψ t₀.ψ)
    (K₁.prod K₂) (hψF l) hUo hUc (hFinB _ ((hok l).ψ))
  choose hm _ _ hm₃ using hex

  have hact : ∀ l (F : B.I → H E B.a B.b → ℂ),
      (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
      heckeAct (hm l) F = convF B.ν (tΛ l).ψ F := fun l F hF => by
    rw [← hm₃ l F hF, (hFinA _ F hF).2 _ (hok l).ψ]
  have heig : ∀ l k, heckeAct (hm l) (f k) = r l k • f k := fun l k => by
    rw [hact l (f k) (hflev k), hr l k]

  have hcons : ∀ l l', hm l = hm l' → ∀ k, r l k = r l' k := fun l l' e k =>
    smul_cancel (hf0 k) (by rw [← heig l k, ← heig l' k, e])
  have hcons₀ : ∀ l l', hm l = hm l' → r₀ l = r₀ l' := fun l l' e =>
    tendsto_nhds_unique (hlim l) (by
      have : r l = r l' := funext (hcons l l' e)
      rw [this]; exact hlim l')
  let lam : ℕ → HeckeM E B.a B.b B.I → ℂ := fun k h => if hh : ∃ l, hm l = h then r hh.choose k else 0
  let lam₀ : HeckeM E B.a B.b B.I → ℂ := fun h => if hh : ∃ l, hm l = h then r₀ hh.choose else 0
  have hlam : ∀ l k, lam k (hm l) = r l k := fun l k => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam, dif_pos hh]
    exact hcons _ _ hh.choose_spec k
  have hlam₀ : ∀ l, lam₀ (hm l) = r₀ l := fun l => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam₀, dif_pos hh]
    exact hcons₀ _ _ hh.choose_spec
  refine ⟨hm, lam, lam₀, ?_, ?_, fun l F hF => ⟨hact l F hF, hlam₀ l⟩⟩
  · rintro k _ ⟨l, rfl⟩
    rw [hlam, heig]
  · rintro _ ⟨l, rfl⟩
    simp only [hlam, hlam₀]
    exact hlim l

theorem val_tendsto (hVC : ValCont) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B)
    (ht : t.Ok) (χak : ℕ → InfinitePlace E → Inf B.a) (χa : InfinitePlace E → Inf B.a)
    (χbk : ℕ → InfinitePlace E → Inf B.b) (χb : InfinitePlace E → Inf B.b)
    (hA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)))
    (hB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m))) :
    Tendsto (fun k => t.val (χak k) (χbk k)) atTop (𝓝 (t.val χa χb)) := by
  unfold PT.val valA
  refine Tendsto.mul (tendsto_finsetProd _ fun v _ => ?_) (tendsto_finsetProd _ fun v _ => ?_)
  · exact hVC B.a B.μa (B.Ma v) (t.ka v) (t.va v) t.T (fun k => χak k v) (χa v) (ht.ka v) (hA v)
  · exact hVC B.b B.μb (B.Mb v) (t.kb v) (t.vb v) t.T (fun k => χbk k v) (χb v) (ht.kb v) (hB v)


theorem blockOut_lim (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv) (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint)
    (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ W₁' : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ W₂' : Submodule ℂ (Kinf E B.b → ℂ)) (hW₁ : W₁ ≤ W₁') (hW₂ : W₂ ≤ W₂')
    (Ω₁ Ω₂ Ω₁' Ω₂' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (hΩ₁ : ∀ M, Ω₁ M ⊆ Ω₁' M) (hΩ₂ : ∀ M, Ω₂ M ⊆ Ω₂' M)
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hEB : EFinalAt E B.a B.b W₁' W₂' Ω₁ Ω₂ K₁ K₂ Θ₁ Θ₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (ha₀ : g a₀ = Sum.inr t₀)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hχ0 : χ (genE g X a₀) ≠ 0)
    (hreg : ∀ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, 1 ≤ m → 0 < B.a → GlobalTheory.Dec.gelfVal (χa v s) m = χ (genE g X (der v s m).1) / χ (genE g X a₀)) →
      (∀ v s m, 1 ≤ m → 0 < B.b → GlobalTheory.Dec.gelfVal (χb v s) m = χ (genE g X (der v s m).2) / χ (genE g X a₀)) →
      RealSym (mOf χa) ∧ RealSym (mOf χb) ∧ ∀ τ, GapM (mOf χa τ) ∧ GapM (mOf χb τ))
    (hK : PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ) :
    Nonempty (BlockOut B g a₀ t₀ X tX jX χ K₁ K₂ W₁' W₂' Θ₁ Θ₂ Ω₁' Ω₂') := by
  obtain ⟨M, sk, f, χak, χbk, hsg, hsX, hgA, hgB, hk⟩ := hK
  have h₀ : t₀.Ok := by have := hok a₀; rw [ha₀] at this; exact this

  choose χa hχa using fun v s => hIL B.a (fun k => χak k v s) _ (hgA v s)
  choose χb hχb using fun v s => hIL B.b (fun k => χbk k v s) _ (hgB v s)
  obtain ⟨hRa, hRb, hGap⟩ := hreg χa χb (fun v s m h1 h2 => by rw [hχa, if_pos ⟨h1, h2⟩])
    (fun v s m h1 h2 => by rw [hχb, if_pos ⟨h1, h2⟩])
  have cA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)) :=
    fun v s m => by rw [hχa]; exact hgA v s m
  have cB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m)) :=
    fun v s m => by rw [hχb]; exact hgB v s m

  let Λ := {y : Γ // ∃ t, g y = Sum.inr t ∧ FinType t₀ t} ⊕ Unit
  let tΛ : Λ → PT B := Sum.elim (fun y => y.2.choose) (fun _ => tX)
  have hokΛ : ∀ l, (tΛ l).Ok := by
    rintro (y | _)
    · have := hok y.1; rw [y.2.choose_spec.1] at this; exact this
    · exact htX
  let r : Λ → ℕ → ℂ := Sum.elim (fun y k => sk k (genE g X y.1) / sk k (genE g X a₀))
    (fun _ k => sk k (XE g X) / sk k (genE g X a₀) ^ jX)
  let r₀ : Λ → ℂ := Sum.elim (fun y => χ (genE g X y.1) / χ (genE g X a₀)) (fun _ => χ (XE g X) / χ (genE g X a₀) ^ jX)
  have hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k := by
    rintro (y | _) k
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.1 y.1 _ y.2.choose_spec.1 y.2.choose_spec.2
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l)) := by
    rintro (y | _)
    · exact (hsg y.1).div (hsg a₀) hχ0
    · exact hsX.div ((hsg a₀).pow jX) (pow_ne_zero _ hχ0)
  have hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x :=
    fun k i u hu x => ((hk k).2.2.2.2.2.1 i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨hm, lam, lam₀, hHe, hHl, hHF⟩ := hecke_setup hFH hBO hFin B K₁ K₂ o₁ c₁ o₂ c₂ t₀ h₀ cK hcK hψ₀ Λ tΛ hokΛ f
    (fun k => (hk k).2.2.1) hflev r r₀ hr hlim

  obtain ⟨s₁, s₂, F, g₁, g₂, u₁, u₂, l₁, l₂, i₁, i₂, hF0, hFm, hFt, hFh⟩ := hEB B.D B.I M
    (fun k => mOf (χak k)) (fun k => mOf (χbk k)) (mOf χa) (mOf χb) (Set.range hm) lam lam₀ f
    (Set.countable_range hm) (fun N _ _ ν _ K' W' R' hK' hW' => hRE E N ν K' W' R' hK' hW')
    (fun k => (hk k).2.1) (fun k => (hk k).2.2.1) (fun k => (hk k).2.2.2.1) (fun k => (hk k).2.2.2.2.1)
    (fun k i => typeH_mono hW₁ hW₂ ((hk k).2.2.2.2.2.1 i)) (fun k => (hk k).2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.2.1)
    hHe (fun τ ε hε => (mclose_of hIC χak χa cA τ ε hε).and (mclose_of hIC χbk χb cB τ ε hε))
    hRa hRb hGap hHl
  have hFlev : ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x :=
    fun i u hu x => (hFt i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hFeig : ∀ l, convF B.ν (tΛ l).ψ F = r₀ l • F := fun l => by
    obtain ⟨e1, e2⟩ := hHF l F hFlev
    rw [← e1, hFh _ ⟨l, rfl⟩, e2]
  have L₁ : s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₁ M hW', ht⟩) s₁ l₁
  have L₂ : s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₂ M hW', ht⟩) s₂ l₂
  refine ⟨⟨s₁, s₂, F, χa, χb, g₁, g₂, u₁, u₂, L₁, L₂, i₁, i₂, ⟨herm_of_realSym χa hRa, herm_of_realSym χb hRb⟩,
    hF0, hFm, hFt, ?_, ?_, ?_⟩⟩
  · intro x t hx hft
    have l := (Sum.inl ⟨x, t, hx, hft⟩ : Λ)
    have ht : (Classical.choose (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)) = t := by
      have := (Classical.choose_spec (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)).1
      exact Sum.inr_injective (this.symm.trans hx)
    have := hFeig (Sum.inl ⟨x, t, hx, hft⟩)
    simp only [tΛ, r₀, Sum.elim_inl, ht] at this
    exact this
  · intro x t hx hat
    have hto : t.Ok := by have := hok x; rw [hx] at this; exact this
    have e : ∀ k, t.val (χak k) (χbk k) = sk k (genE g X x) := fun k =>
      (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.2 x t hx hat
    have h1 := val_tendsto hVC B t hto χak χa χbk χb cA cB
    simp only [e] at h1
    exact tendsto_nhds_unique (hsg x) h1
  · exact hFeig (Sum.inr ())

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Limitb

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

theorem sup_one_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ)) :
    W ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)} ≠ ⊥ := by
  intro h
  have hm : (fun _ => (1 : ℂ)) ∈ W ⊔ Submodule.span ℂ {fun _ : Kinf E a => (1 : ℂ)} :=
    Submodule.mem_sup_right (Submodule.subset_span rfl)
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 1
  simp at this

theorem kTypes_insert {E : Type} [Field E] [NumberField E] [IsCMField E] {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))}
    (h : KTypes E Ω) : KTypes E (fun M => insert ⊥ (Ω M)) := by
  intro M
  refine ⟨(h M).1.insert _, fun W hW => ?_⟩
  rcases hW with rfl | hW
  · infer_instance
  · exact (h M).2 W hW


theorem readLimit_main (hPack : Pack) (hEF : EFinal) (hAV : ActVal) (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv)
    (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt) : ReadLimit := by
  intro E _ _ _
  choose Wf₁ Wf₂ hWfd₁ hWfd₂ hP using fun a b (Ma : Mods E a) (Mb : Mods E b) => hPack E a b Ma Mb
  let V₁ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E a → ℂ) := fun a b Ma Mb =>
    Wf₁ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  let V₂ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E b → ℂ) := fun a b Ma Mb =>
    Wf₂ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  have hV₁ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₁ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₁ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  have hV₂ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₂ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₂ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  choose Ωf₁ Ωf₂ hΩ₁ hΩ₂ hEr using fun a b (Ma : Mods E a) (Mb : Mods E b) =>
    hEF E a b (V₁ a b Ma Mb) (V₂ a b Ma Mb) (hV₁ a b Ma Mb) (hV₂ a b Ma Mb)
  let Θf₁ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose else fun _ => ∅
  let Θf₂ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose_spec.choose else fun _ => ∅
  have hΘ₁ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₁ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  have hΘ₂ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₂ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  refine ⟨V₁, V₂, fun a b Ma Mb M => insert ⊥ (Ωf₁ a b Ma Mb M), fun a b Ma Mb M => insert ⊥ (Ωf₂ a b Ma Mb M),
    Θf₁, Θf₂, fun a b Ma Mb => ⟨hV₁ a b Ma Mb, hV₂ a b Ma Mb, kTypes_insert (hΩ₁ a b Ma Mb),
      kTypes_insert (hΩ₂ a b Ma Mb), fun M => ⟨⟨⊥, Set.mem_insert _ _⟩, ⟨⊥, Set.mem_insert _ _⟩⟩,
      sup_one_ne_bot _, sup_one_ne_bot _⟩, fun a b Ma Mb K₁ K₂ o₁ o₂ => ?_, ?_⟩
  · rw [hΘ₁ a b Ma Mb K₁ K₂ o₁ o₂, hΘ₂ a b Ma Mb K₁ K₂ o₁ o₂]
    exact ⟨(hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.1, (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.1⟩
  intro B K₁ K₂ o₁ c₁ o₂ c₂ Γ _ g a₀ t₀ bump cK der X tX jX χ _hab hok htX hXe hjX ha₀ hbump _htype hka0 hkb0
    hcK hψ₀ hderA hderB hcomm hXc hXs hχn hχ0 hreg
  rw [hΘ₁ _ _ _ _ K₁ K₂ o₁ o₂, hΘ₂ _ _ _ _ K₁ K₂ o₁ o₂]
  have hEB := (hEr B.a B.b B.Ma B.Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.2
  have hK := perK hAV hBO hCM hFin hReal B (Wf₁ B.a B.b B.Ma B.Mb) (Wf₂ B.a B.b B.Ma B.Mb) K₁ K₂ o₁ c₁ o₂ c₂
    (hP B.a B.b B.Ma B.Mb) Γ g a₀ t₀ bump cK der X tX jX χ hok htX hXe hjX ha₀ hbump hka0 hkb0 hcK hψ₀ hderA hderB
    hcomm hXc hXs hχn hχ0
  exact blockOut_lim hFH hVC hIC hIL hRE hBO hFin B (Wf₁ B.a B.b B.Ma B.Mb) (V₁ B.a B.b B.Ma B.Mb)
    (Wf₂ B.a B.b B.Ma B.Mb) (V₂ B.a B.b B.Ma B.Mb) le_sup_left le_sup_left (Ωf₁ B.a B.b B.Ma B.Mb) (Ωf₂ B.a B.b B.Ma B.Mb)
    (fun M => insert ⊥ (Ωf₁ B.a B.b B.Ma B.Mb M)) (fun M => insert ⊥ (Ωf₂ B.a B.b B.Ma B.Mb M))
    (fun M => Set.subset_insert _ _) (fun M => Set.subset_insert _ _) K₁ K₂ _ _ o₁ c₁ o₂ c₂ hEB Γ g a₀ t₀ cK der X tX jX χ
    hok htX ha₀ hcK hψ₀ hχ0 hreg hK

theorem convMulSt_holds : ConvMulSt := fun _ _ _ _ _ _ D _ _ Φ₁ Φ₂ h₁ h₂ f hf => conv_mulM D Φ₁ Φ₂ h₁ h₂ f hf

theorem readLimit_of (e2 : PositivityTheory.Rg.BcB.E.E2) (pk : Pack) (ef : EFinal) (av : ActVal) (fh : FinHecke) (vc : ValCont)
    (ic : InfConv) (il : InfLim) (re : ReproEx) (tm : TensMul) (bo : BlockOperatorsProductAdjoint) (bw : BlockWordOperators) (bs : BlockLinearCombinations)
    (aw : AdjWords) : ReadLimit :=
  readLimit_main pk ef av fh vc ic il re bo convMulSt_holds finSt (realise e2 tm bo bw bs aw)

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end
