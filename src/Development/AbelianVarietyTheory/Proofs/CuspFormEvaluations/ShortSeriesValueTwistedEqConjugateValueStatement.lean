module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.XLaterHarmonicNotMemSpan
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsNabTwist

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem isNab_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → IsNab Xo c (fun {S} _ _ y k F α => (nab (twPt h y) k F α).val) := by
  intro E _ _ _ H Dw l Xo c ta h _ nab hn
  refine ⟨hn.1, fun S _ _ iQ y => ?_⟩
  letI : Algebra ℚ (Tw ta S) := iQ
  obtain ⟨C, h1, h2⟩ := hn.2 (Tw ta S) (twPt h y)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.GalTw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortSeriesValueTwistedEqConjugateValue

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

theorem colSum_eq_of_isNab (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab nab' : NabV Xo c) (h : IsNab Xo c nab) (h' : IsNab Xo c nab') {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : ℤ) (k : ℕ) (hK : K = (k : ℤ))
    (G : Fin n → LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
  subst hK
  exact GlobalTheory.NabUniqCompare.thExprUniqSt_iff_top.1 (Formalism.MainNotions.ModuliIntegralCharts.H1.thExprUniq_of_chartIndep2 hC) E H Dw l Xo c
    nab nab' h h' S y k n G P
    ⟨(GlobalTheory.NabUniqCompare.isHarmonic_iff_cmType c P).2 hP.1, hP.2.1, a, hP.2.2⟩

theorem coeffAutFixesCMConjugatesAndBase_symm {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {l : Level H} {c : Coeff l} {ta : c.F ≃+* c.F} (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => (ta.symm_apply_eq).2 (h.emb τ a).symm, fun a => (ta.symm_apply_eq).2 (h.base a).symm⟩

theorem algebraMap_tw_symm {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (x : K) :
    (algebraMap K (Tw ta.symm S) (ta x)).val = algebraMap K S x := by
  change algebraMap K S (ta.symm (ta x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem shortValAt_conj : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  intro hC E _ _ _ H Dw l Xo c ta h _ nab hnab n a P hP w Λ b N S _ _ y v hv
  obtain ⟨S', i1, i2, φ, y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, hv⟩ := hv
  have h' : Fixes c ta.symm := coeffAutFixesCMConjugatesAndBase_symm h
  have hnab' := GlobalTheory.GalTw.isNab_twist E H Dw l Xo c ta.symm h' nab hnab
  let φ' : S →ₐ[c.F] Tw ta.symm S' :=
    { toRingHom := φ.toRingHom
      commutes' := fun x => by
        have := φ.commutes (ta.symm x)
        change φ (algebraMap c.F S (ta (ta.symm x))) = _ at this
        rw [RingEquiv.apply_symm_apply] at this
        exact this }
  have hinj : Function.Injective (ta : c.F →+* c.F) := ta.injective
  have hsupp : (MvPolynomial.map (ta : c.F →+* c.F) P).support = P.support :=
    MvPolynomial.support_map_of_injective P hinj
  have hdeg : (MvPolynomial.map (ta : c.F →+* c.F) P).totalDegree = P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsupp]
  refine ⟨Tw ta.symm S', inferInstance, inferInstance, φ', twPt h' y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, ?_⟩
  have e1 : (ta b)⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹ = ta (b⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) := by
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  rw [hsupp, hdeg, e1]
  refine hv.trans ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine finsum_congr fun q => ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (colSum_eq_of_isNab hC Xo c _ _ hnab hnab' a P hP S' y' _ (N ^ 2) (Nat.cast_pow N 2).symm (F q i)).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  exact congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm rfl

end GlobalTheory.GalTw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortSeriesValueTwistedEqConjugateValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem _root_.GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  first | exact @GlobalTheory.GalTw.shortValAt_conj | exact GlobalTheory.GalTw.shortValAt_conj | (intros; apply GlobalTheory.GalTw.shortValAt_conj <;> assumption)
end
end
