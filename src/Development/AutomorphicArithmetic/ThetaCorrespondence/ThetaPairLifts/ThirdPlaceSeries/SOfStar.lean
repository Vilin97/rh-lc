module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
public import Development.AutomorphicArithmetic.NaturalDivisibility.ExistsContinuousRingEquivPadicOfTotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OfStar

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem star_guard {y : WD h} (k : NcW y) : (IsQpBig w y.lpDim ∧ TmW y ∧ UpperTheory.GalStar.Sqf y) ∨ Tor y := by
  by_cases hs : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧
      (y.lpDim = 1 ∨ 16 * y.lpDim ^ 2 < p)
  · have ht : thr w y.lpDim = 2 := if_pos hs
    obtain ⟨p, hp, hw, hc, hb⟩ := hs
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨i, hi⟩ := UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split E w p hw hc
    exact Or.inl ⟨⟨p, inferInstance, i, hi, hb⟩, k.1, fun γ hγ hg z hz => k.2.2 γ hγ hg z (by rwa [ht])⟩
  · exact Or.inr (tor_of_ncW (if_neg hs) k)

theorem tor_of_unr {y : WD h} (u : y.unr) : Tor y := fun s t => by
  have hd : deg ⁅s, t⁆ = 0 := by simp [commutatorElement_def]
  have := inePol_of_unr u (deg_eq_zero_iff.1 hd)
  rwa [WD.inePol_of_mem _ (⁅s, t⁆ : ↥(Weil h)).2] at this

theorem away_nice {x y : WD h} (a : AwayB x y) (k : NcW y) :
    x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g := by
  rcases star_guard k with ⟨q, t, s⟩ | t
  · exact a.tame0 q t s k.2.1
  · rw [a.tor t k.2.1]; exact ⟨k.2.1, fun _ _ => rfl⟩

theorem aw_of_away {x y : WD h} (a : AwayB x y) : Aw x y :=
  ⟨a.dim, fun u => a.tor (tor_of_unr u) (WD.unr_mono0 _ u), fun k => (away_nice a k).2, fun k => (away_nice a k).1⟩
end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]


end UpperTheory.GalS
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOfStar

section

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
omit [IsCMField E] [Fact l.Prime] in
theorem star_guard'_alt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (k : NcW (rc (algNorm σ))) :
    (IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ UpperTheory.GalStar.Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hrc
  have e : (rc (algNorm σ)).lpDim = a := H.dim _
  have := star_guard k
  rwa [e] at this
theorem isGalU_of_props_alt {π : CuspSub E a} (χ : HChar (maximalRealSubfield E)) {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsB _root_.UpperTheory.One.M.recT π ι r wt HT) :
    _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT :=
  ⟨H.cont, H.ss, fun w hl A h rc hrc σ hσ => aw_of_away (H.away w hl A h rc hrc σ hσ), H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have k := H.above P AI T w A h O Bw hj
      ⟨fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).1,
        fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.1, fun σ hσ hs => (k.crys σ hσ hs).1⟩⟩
theorem pairU_of_star_alt (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.PairUAlt := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt χ k⟩
theorem carU_of_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.CarUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  have hpol := isPolarized_of_isCsd hc
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a (by omega) π _ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E _) (hGK E a _) hpol.dual⟩
  refine ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt _ k, fun P AI T w _ A h O _ _ _ Bw hj σ hσ rc hrc n => ?_⟩
  have b := ((k.above P AI T w A h O Bw hj).nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.2
  exact ⟨b.dim, fun _ => (away_nice b n).1, fun _ _ => (away_nice b n).2⟩
theorem field_of_starFull_alt (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : GlobalTheory.Published.LocalConverseGL)
    (_ : GlobalTheory.Published.LanglandsExhaustionGL) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.PairUAlt := _root_.UpperTheory.GalS.pairU_of_star_alt H
theorem ofDual_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.CarUAlt := _root_.UpperTheory.GalS.carU_of_star_alt hGK H
end UpperTheory.GalS
end
end
end
end
