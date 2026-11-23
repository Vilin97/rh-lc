module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOn

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.IntFrComp

open AlgebraicGeometry

theorem exists_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  intro E _ _ _ H Dw l Xo c T io y
  letI := io.toAlgebra
  let s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  refine ⟨⟨irreducibleComponent (GlobalTheory.AllWt.ptF y.1 s₀), irreducibleComponent_mem_irreducibleComponents _⟩,
    fun s => ?_⟩
  obtain rfl : s = s₀ := Subsingleton.elim (α := PrimeSpectrum T.Fr) s s₀
  exact mem_irreducibleComponent

end GlobalTheory.IntFrComp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOnStatement

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.exists_component_integral_framedPoint_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  first | exact @GlobalTheory.IntFrComp.exists_liesOn | exact GlobalTheory.IntFrComp.exists_liesOn | (intros; apply GlobalTheory.IntFrComp.exists_liesOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwMulOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_eq_of_agree {Z : Comp Xo c} {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w)
    {f g : Rul Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) :
    v g = v f := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c g y.1) = nval T.V e (evR Xo c f y.1)
  rw [h _ y.1 hy.2]

theorem exists_latW_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c)
    (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G,
    ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG Z t w v hv f hf
  obtain ⟨f', hres, hlat⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z G f
  have hf'lat := hlat hf
  obtain ⟨a, ha0, hva, hpos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F t.lo t.finite_lo w
  obtain ⟨φ, hφ, -, hint, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ t G hG
  have hg := hint a ha0 hpos f' hf'lat (a • φ f') (by rw [Submodule.coe_smul])
  refine ⟨⟨(a • φ f' : cuspOn U Z (G + G₀)), cuspOn_le U Z (G + G₀) (a • φ f').2⟩, (mem_latOn U).1 hg, ?_⟩
  have hV := isVal_valOn hv
  obtain ⟨b, hb, -, -, hbhi⟩ := t.exists_val hv
  have e1 : v (f' : Rul Xo c) = v (f : Rul Xo c) := val_eq_of_agree hv (hres)
  show v ((a • φ f' : cuspOn U Z (G + G₀)) : Rul Xo c) ≤ _
  rw [Submodule.coe_smul, hV.smul _ _ ha0, hφ, hV.mul, e1, hb, hva]
  rw [← add_assoc, add_comm (((-(⌊t.lo w⌋ : ℝ) : ℝ)) : EReal) (v (f : Rul Xo c)), add_assoc, ← EReal.coe_add]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.TwMulOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLeStatement

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.exists_twistingSection_mul_lattice_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c) (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G, ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.TwMulOne.exists_latW_val_le | exact GlobalTheory.TwMulOne.exists_latW_val_le | (intros; apply GlobalTheory.TwMulOne.exists_latW_val_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe

section

@[expose] public section



noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefTwist

theorem vAdd_natCast_pos {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q ≠ 0) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 0 < vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem _).2 hw
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (w.valuation K).ne_zero_iff.2 (Nat.cast_ne_zero.2 hq)
  have h2 := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vAdd
  omega

theorem nval_le_add_of_mul {T : CDVR} {e n : ℕ} {m s k : ℝ} (he : 0 < e) (hm : 0 < m) (hn : (n : ℝ) = e * m)
    (hs : s ≤ k * m) {a b : T.Fr} (h : nval T.V e b ≤ nval T.V e a + (s : EReal)) :
    nval T.V n b ≤ nval T.V n a + (k : EReal) := by
  by_cases ha : a = 0
  · rw [ha, nval_zero, EReal.top_add_coe]; exact le_top
  rw [nval_of_ne ha, ← EReal.coe_add] at h ⊢
  by_cases hb : b = 0
  · rw [hb, nval_zero] at h; exact absurd h (not_le.2 (EReal.coe_lt_top _))
  rw [nval_of_ne hb, EReal.coe_le_coe_iff] at h ⊢
  have he' : (0 : ℝ) < e := Nat.cast_pos.2 he
  rw [hn, ← div_div, ← div_div, div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

theorem refExp_vp_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG cst k q hq t ht
  refine (refExp_vp_le_iff U).2 fun la T io e ho y hy φ hφ => ?_
  have h0 := (refExp_vp_le_iff U).1 (le_refl (refExp_vp U cst G q)) la T io e ho y hy φ hφ
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_integral_framedPoint_liesOn E H Dw l Xo c T io y
  have hv : (fun f => nval T.V e (evI y f)) ∈ valOn Z la.1 := ⟨PtV.mk la.1 ho y ⟨hy, hZ⟩ () trivial, rfl⟩
  have hm : 0 < vAdd la.1 (q : c.F) := vAdd_natCast_pos hq.ne_zero la.2
  have hq' : vV T.V (q : T.Fr) = (e : ℤ) * vAdd la.1 (q : c.F) := by
    rw [← map_natCast io q]; exact ho.2 _
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * (vAdd la.1 (q : c.F) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq' ▸ mul_nonneg (Int.natCast_nonneg e) hm.le), hq']
    push_cast; rfl
  have hd : depthAt_vp U (G + G₀) q y ≤ depthAt_vp U G q y + (k : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    obtain ⟨g, hg, hle⟩ := GlobalTheory.T.exists_twistingSection_mul_lattice_value_le E H Dw l Xo c r U hU x G G₀ hG Z (t Z) la.1 _ hv f hf
    exact (iInf₂_le g hg).trans (nval_le_add_of_mul ho.1 (Int.cast_pos.2 hm) hn (ht Z la.1 la.2) hle)
  rw [add_right_comm]
  exact hd.trans (add_le_add h0 le_rfl)

end GlobalTheory.RefTwist

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLeStatement

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.baseLocusExponent_twistingSection_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  first | exact @GlobalTheory.RefTwist.refExp_vp_add_le | exact GlobalTheory.RefTwist.refExp_vp_add_le | (intros; apply GlobalTheory.RefTwist.refExp_vp_add_le <;> assumption)
end
end
