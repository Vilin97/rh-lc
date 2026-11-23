module

public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortUnits

open GlobalTheory.LatticeIndex GlobalTheory.TrivLattice

section Val
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem valuation_nat {k : ℕ} (hk : (k : 𝓞 K) ∉ la.asIdeal) : la.valuation K (k : K) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 K) K)]
  exact la.valuation_eq_one_iff_notMem.2 hk

theorem not_mem_of_coprime' {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) :
    (b : 𝓞 K) ∉ la.asIdeal := fun hb => by
  obtain ⟨u, v, e⟩ : IsCoprime (a : 𝓞 K) (b : 𝓞 K) := h.cast
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ ha) (la.asIdeal.mul_mem_left _ hb)))

end Val

theorem vLa_beta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (la : HeightOneSpectrum (𝓞 c.F)) (hA : PullbackSections.AdaptAt Λ la) (β : c.F)
    (hβ : BetaIs (Dw := Dw) c Λ β) : vLa la β = 0 := by
  obtain ⟨k, hk, hk1, hk2⟩ := hA
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  let w := la.valuation c.F
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hw ⟨_, map_isIntegral_int (embF c τ) r.isIntegral_coe⟩
  have hnat : ∀ τ, w.comap (embF c τ) (k : E) = 1 := fun τ => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valuation_nat la hk
  have hm : ∀ (A : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := fun A a1 a2 => by
    have := hasMax_prod hw Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) fun τ => by
      obtain ⟨a, y, hy, b⟩ := detSet_max _ (hwτ τ) A (hnat τ) a1 a2
      have h : HasMax w (idealAt c A τ) 1 := by
        refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
        rintro _ ⟨y, hy, rfl⟩
        exact a y hy
      simpa using h.pow hw (Dw.mult τ)
    simpa using this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {β}) (w β) := hasMax_span hw (by simp) (by simp)
  have f1 := hb.mul (hm Λ.La h1 h2)
  rw [hβ] at f1
  have f := f1.unique (hm Λ.Ln (fun v hv => h1 v hv.1)
    (fun v hv => ⟨h2 v hv, (stdLat E n).toAddSubgroup.nsmul_mem hv k⟩))
  rw [_root_.mul_one] at f
  have f' : la.valuation c.F β = 1 := f
  simp [vLa, f']

theorem vLa_betaH {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ} (Λ : GenLat D.host.E n)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D)) (hA : PullbackSections.AdaptAt Λ la) :
    vLa la (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 0 := by
  have h := hF.sh.beta j hj n (hF.p.kPsi j hj) Λ hU hT
  refine vLa_beta (Dw := T.Q.Dw j) T.Q.c Λ la hA _ ?_
  unfold betaH
  rw [dite_eq_left h]
  exact h.choose_spec.2.1

end GlobalTheory.ShortUnits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.BetaInvIntegral

theorem betaH_inv_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  intro D T hF j hj n Λ σ p hp hU hT hTp
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  obtain ⟨M, hM, hint⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hp
    (betaH (Dw := T.Q.Dw j) T.Q.c Λ)⁻¹ (fun w hw => by
      obtain ⟨k, hk, h1, h2⟩ := hTp
      have hA : ReciprocityTheory.ChartRestriction.G.PullbackSections.AdaptAt Λ w :=
        ⟨k, GlobalTheory.ShortUnits.not_mem_of_coprime' w hk.symm hw, h1, h2⟩
      have hv := GlobalTheory.ShortUnits.vLa_betaH T hF j hj Λ w hU hT hA
      have hne : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) ≠ 0 := by simpa using hβ
      have h1' : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 1 := by
        rw [← WithZero.exp_log hne]
        simp only [vLa, neg_eq_zero] at hv
        rw [hv]; rfl
      rw [map_inv₀, h1', inv_one])
  refine ⟨M, hM, ?_⟩
  have := map_isIntegral_int σ hint
  simpa [map_mul, map_inv₀, map_natCast] using this

end GlobalTheory.BetaInvIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  first | exact @GlobalTheory.BetaInvIntegral.betaH_inv_integral | exact GlobalTheory.BetaInvIntegral.betaH_inv_integral | (intros; apply GlobalTheory.BetaInvIntegral.betaH_inv_integral <;> assumption)
end
end
