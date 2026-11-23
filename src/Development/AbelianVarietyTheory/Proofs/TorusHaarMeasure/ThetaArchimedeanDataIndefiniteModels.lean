module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBounds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyTorusAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExtAllInputs
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExistsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Parity
public import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjHalfIntegralGenerator

section

@[expose] public section

namespace GlobalTheory.CMConjugationOfSquareRoot

open NumberField Complex
open scoped ComplexConjugate

theorem conj_eq_neg_of_sq_eq_neg {z : ℂ} {d : ℝ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    conj z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h0 | h0
    · exact h0
    · rw [h0] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre0]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem complexConj_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E ((H.rt : 𝓞 E) : E) = -((H.rt : 𝓞 E) : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq_eq_neg (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  simpa using h

theorem conj_halfIntegralGenerator (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc ((H.w0 : 𝓞 E) : E) = (1 : E) - ((H.w0 : 𝓞 E) : E) := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    push_cast at this
    exact this
  have h3 : (2 : E) * IsCMField.complexConj E (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, complexConj_rt] at this
    have h22 : IsCMField.complexConj E (2 : E) = 2 := map_ofNat _ 2
    rw [h22] at this
    rw [this]; ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.cc
  apply mul_left_cancel₀ (two_ne_zero : (2 : E) ≠ 0)
  rw [h3, mul_sub, h2]; ring

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ReciprocityTheory.ChartRestriction.G.FD.cc (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) = (1 : E) - (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) := fun H => conj_halfIntegralGenerator H

end GlobalTheory.CMConjugationOfSquareRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmulMemLattice

section

@[expose] public section

namespace GlobalTheory.SmulMemOfSpan

open NumberField

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin r → E))) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ (c : E) • v ∈ L := by
  have hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L := by
    intro n w hw
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact L.smul_mem n hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]
    exact hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : ((c * d : RingOfIntegers E) : E) • (x + y) =
        (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
    rw [e]
    exact L.add_mem (hL d _ hcx) (hL c _ hdy)
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨n, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) a
    have hy0 : algebraMap (RingOfIntegers E) E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩
    have e : ((y * c : RingOfIntegers E) : E) •
        ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) =
        (n : E) • ((c : E) • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      field_simp
    rw [e]
    exact hL n _ hcx

theorem exists_smul_mem_lattice : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E), ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ (↑c : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by
  intro E _ _ _ r X v
  refine exists_smul_mem_of_span X.Λ v ?_
  rw [X.Λ_span]
  exact Submodule.mem_top

end GlobalTheory.SmulMemOfSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaBound

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem theta_bound_tStatement : TStatement :=
  tOf ext_all_inputs GlobalTheory.T.greedy_splitting_principal_torus_exists (gSup ext_all_inputs.1) dim

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjCmHalfIntegralGeneratorEqOneSub

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_multiple_mem (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ (c : E) • v ∈ X.Λ :=
  _root_.GlobalTheory.SmulMemOfSpan.exists_smul_mem_lattice X v

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (x y : Fin r → E) :
    herm G (a • x) (b • y) = a * ReciprocityTheory.ChartRestriction.G.FD.cc b * herm G x y := by
  simp only [herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_isIso (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {ρ : ℕ} (cu : FJ.CuspFD X ρ) (hρ : 0 < ρ) :
    ∃ ξ : Fin r → E, X.IsIso ξ := by
  obtain ⟨c, hc, hm⟩ := exists_multiple_mem X (cu.e ⟨0, hρ⟩)
  refine ⟨_, hm, by rw [herm_smul_smul, cu.iso, mul_zero], ?_⟩
  exact smul_ne_zero (by simpa using hc) (cu.ind.ne_zero _)

theorem conj_cmHalfIntegralGenerator_eq_one_sub (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ReciprocityTheory.ChartRestriction.G.FD.cc (H.w0 : E) = 1 - (H.w0 : E) :=
  _root_.GlobalTheory.CMConjugationOfSquareRoot.main H

theorem even_im_hermitian_sub (X : DataX E r) (w0 : 𝓞 E) (hw : ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) = 1 - (w0 : E)) :
    ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k :=
  _root_.UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub X w0 hw

end General

theorem extra_weight_exists : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), GamAt T.toCore → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → j < D.R.m → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE → 16 ≤ D.host.rdE → D.R.m ^ 4 ≤ D.R.f → ∀ k : (T.U j T.σ₀).Comp, BasePotentialExistence ((T.U j T.σ₀).X k) (de2W ((T.U j T.σ₀).X k)) D.R.r (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f))) := by
  intro D T h j hj large₂ w hG hP hL hrn hjm hf2 hrd hm4 k
  obtain ⟨e, -⟩ := GlobalTheory.CuspDataBounds.cusp_data_bounds D T h hG large₂ j hj w hP hL hrn T.σ₀ T.good_σ₀
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hcard : ((T.U j T.σ₀).X k).Ψ.card = D.R.f := by
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j T.σ₀).X k).cmType
    rw [hfr] at h2c
    omega
  have hPf : ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    omega
  have hPr : ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E = D.host.rdE := rfl
  have hp0 : ((T.U j T.σ₀).X k).p0 = D.R.m - j :=
    ((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by
      have hp : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      omega
    exact_mod_cast this
  obtain ⟨cu⟩ := h.cuNe j hj k
  have hρ : 0 < WeightFamilies.rho D j := by
    show 0 < D.R.m - j
    omega
  have key := GlobalTheory.ThetaWeight.exists_weight GlobalTheory.theta_bound_tStatement D.host.E D.R.r (e k).toX
    (exists_isIso _ cu hρ)
    ⟨⟨T.Q.H.w0, even_im_hermitian_sub _ _ (conj_cmHalfIntegralGenerator_eq_one_sub T.Q.H)⟩, by rw [hPf, hPr]; nlinarith, by rw [hPf, hPr]; exact hf2,
      by rw [hPr]; exact hrd, D.R.m, by omega, by rw [hPf]; exact hm4,
      Or.inl (by show ((T.U j T.σ₀).X k).p0 ≤ _; omega)⟩
  rw [← hcard]
  exact key

end GlobalTheory.ExtraWeight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem thR_pos_of_rank {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hr : 0 < D.R.r) : 0 < thR w := by
  have hf : 0 < D.R.f := GlobalTheory.ArchInputs.f_pos D
  have hfE : I2.PT.f D.host.E = D.R.f := GlobalTheory.ArchInputs.finrank_host D
  have hrd := GlobalTheory.ArchInputs.one_le_rd (E := D.host.E)
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  unfold thR I2.th I2.RR
  rw [hfE]
  positivity

theorem sq_le_of_mul_le_exp {a b i p q : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h : a * b ≤ Real.exp (-i * (p - q))) :
    b ^ 2 ≤ Real.exp (2 * (i * q)) / a ^ 2 * Real.exp (-(2 * i * p)) := by
  have h2 := pow_le_pow_left₀ (mul_nonneg ha.le hb) h 2
  rw [← Real.exp_nat_mul] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← Real.exp_add, ← mul_pow, mul_comm b]
  refine h2.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring




theorem archAt_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → Nonempty (GlobalTheory.Shares.ArchAt h j G.w wF Tn (WeightFamilies.c1 D 7 Tn (cc D large₂ C2 A2 7 wL) j)) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus _ hP hC hjm G hGen hEta
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨n1, n2, n3, n4, -, n6, -⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j _ _ 1 4 0 11 large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp ht hP.page hjm hj.1 (le_trans (by norm_num) hP.df)
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, PLam, lNc, -, -, hw1, w2, hG2, th2, -, hth2, -⟩, -⟩ := hC
  obtain ⟨w1, hG1, th1, -, hth1, -⟩ := hw1 hjm
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0
    (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hP
  obtain ⟨-, -, -, hw, hlow⟩ := hGen
  obtain ⟨hi, ⟨-, het⟩, -, -, harch, -⟩ := hEta
  have hth : 0 < thR wL := thR_pos_of_rank wL (lt_of_lt_of_le (by norm_num) hP.r8)
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hP.hyp hP.page hP.ck).1
  have hL : 2 ≤ large₂.sc.L := by
    obtain ⟨_, _, hsz, -⟩ := hP.page
    exact (GlobalTheory.EtaAn.page_rows D large₂ _ hP.hyp.1 hsz).1
  have hrn : D.R.r ≤ ka.n := ((GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj.1
    hP.hyp).1 ka (by simp)).2.2.1
  refine GlobalTheory.ArchInputs.archAt_nonempty D T h j hj large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 7 _ G.N G.w G.iet G.et w1 w2
    th1 th2 hP.hyp hjm hP.r8 n1 n2 n3 n4 n6 hi hG1 hG2
    (fun k x hx => GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx)
    ((hnz _ G.et het).2 T.σ₀ T.good_σ₀) ((hnz _ th1 hth1).2 T.σ₀ T.good_σ₀) ((hnz _ th2 hth2).2 T.σ₀ T.good_σ₀)
    (fun k => ⟨g0, (hnz _ g0 hg0).2 T.σ₀ T.good_σ₀ k⟩) (fun k => ?_) (fun k => ?_)
    (GlobalTheory.ExtraWeight.extra_weight_exists D T h j hj large₂ ka (GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore) hrows hL hrn hjm
      hP.frd (sixteen_le_rdE_of_parA hP.hyp.1) (by exact_mod_cast lift_index_pow_four_le_degree hP.page))
  · refine ⟨thR wL, Real.exp (2 * (p14R wL * (DF wL : ℝ))) * lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2, hth,
      fun x hx => ?_⟩
    have h1 := hlow T.σ₀ T.good_σ₀ k x hx
    have hs : ∑ m, recNrm (T.U j T.σ₀) (xiR D) (wtA wL) wL.n (G.w m).1 k x ^ 2 =
        lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2 *
          ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]; rfl
    have hpos : 0 < ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (GlobalTheory.BigRec.pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    rw [hs] at h1
    have h2 := GlobalTheory.BigRec.exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos _ _ _) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · refine ⟨thR wL, _, hth, fun x hx => sq_le_of_mul_le_exp (lieFac_pos _ _ _) ?_ (harch T.σ₀ T.good_σ₀ k x hx)⟩
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)

end GlobalTheory.RunJoin
end
end
