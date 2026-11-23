module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobiStatement
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumReCmTypeEqHalfTrace

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by

  rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)

    rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (AddMonoidAlgebra.coeff · μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  change (∑ i, (MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))).coeff μ) = 0 at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocksStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  first | exact @GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | exact GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | (intros; apply GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSectionsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℕ) (a : Fin m → ℂ) (Q : Fin m → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (Q i)) → (∀ x ∈ X.dom, f x = ∑ i, a i * Q i x) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν f x = ∑ i, a i * X.fj la ξ ν (Q i) x := by
  first | exact @GlobalTheory.fj_eq_sum_of_eqOn_dom | exact GlobalTheory.fj_eq_sum_of_eqOn_dom | (intros; apply GlobalTheory.fj_eq_sum_of_eqOn_dom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcKill

theorem sum_cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d ι r U a' n n' La c₁ hG hU hFam hDom hT m a F f hF hB hf hfe
  obtain ⟨⟨hob, -, hpush⟩, ⟨s⟩⟩ := hFam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hid⟩ :=
    GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5 E H Dw l Xo c K₁ d ι r U s.ξ s.ν₀ a' n
      (hK.ev E H Dw l Xo c) hG hU hob s.tan hpush s.rk s.ξ_ne s.beta hDom hT
  refine GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks E H Dw l Xo c K₁ d ι m a F fun x hx => ?_
  have hlin := GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections E r (U.X k) (laU U a' n k) m a (fun i => rdU U (F i) k) (f k) (fun i => hB i k)
    (hfe k) ξ' hiso (fun τ => (τ.1 s.ν₀).re) (fr x) (hfr x hx)
  have htr : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    rw [GlobalTheory.sum_re_cmType_eq_half_trace E r (U.X k) s.ν₀]
    exact s.tr
  have h0 := (hf k).2 ξ' hiso (fun τ => (τ.1 s.ν₀).re) htr (fr x) (hfr x hx)
  have hz : u₁ ^ d.jj ≠ 0 := zpow_ne_zero _ hu
  refine (mul_eq_zero.mp ?_).resolve_right hz
  rw [h0] at hlin
  rw [Finset.sum_mul]
  have : ∀ i, a i * ajAt d ι (F i) x * u₁ ^ d.jj =
      κ x * (a i * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U (F i) k) (fr x)) := by
    intro i
    rw [mul_assoc, hid (F i) (hF i) (hB i k) x hx]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hlin, mul_zero]

end GlobalTheory.ArcKill
end
end
