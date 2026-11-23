module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormThetaGeneratorLeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependence
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruenceStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NonzeroDivisorOfConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependenceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.thetaGenerators_noCommonZero_of_chartIndependence : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  first | exact @GlobalTheory.noCommonZero_of_chartIndep | exact GlobalTheory.noCommonZero_of_chartIndep | (intros; apply GlobalTheory.noCommonZero_of_chartIndep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoBaseComponentShortPolynomialGenerator

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NoBase

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem rank_of_pins {D : D7} {Q : Par D} (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨hp, hq, -⟩ := h.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
  simp only [Ranks.sigW, Ranks.r, Ranks.k]
  omega

theorem log_rdE (D : D7) : Real.log (FD.rdE D.host.E) = lrd D := by
  have hpos : 0 < dE D.host.E := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  unfold FD.rdE lrd
  rw [Real.log_rpow hpos, hostSize_finrank D]
  unfold dE
  push_cast
  ring

theorem mem_span_short (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j)
    (w : WeightFamilies.Wt D j) (hrows : PullbackSections.SupBoundPageRows D large₂ w) (hL : 2 ≤ large₂.sc.L) (hr : D.R.r ≤ w.n)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (hP : P ∈ harmA T.Q.c (wtA w) w.n) :
    P ∈ Submodule.span T.Q.c.F {Q | Q ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
      ∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w} := by
  have hrk := rank_of_pins h.pins hj
  have h2 := PfTies1.DF_wtA_le (T.Q.Dw j) w
  have h3 : (((∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) : ℕ)) : ℝ) = absA w := by simp [absA]
  have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [← h3]; exact_mod_cast h2
  have hDF' : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := by exact_mod_cast h2
  have hfd : FD.fdeg D.host.E = D.R.f := by unfold FD.fdeg; rw [hostSize_finrank D]; omega
  obtain ⟨-, r1, -, -, r4, -, -, r7, r8⟩ := hrows
  have key := (GlobalTheory.StdHarm.harmA_mem_span_short D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n).2
    (hrk ▸ hr) (wtA w) large₂.sc.L hL (by rw [log_rdE]; exact r1) (by rw [hfd]; exact r4)
    (le_trans (Real.log_le_log (by positivity) (by linarith)) r7) r8 P hP
  refine Submodule.span_mono ?_ key
  intro Q hQ
  refine ⟨hQ.1, fun σ' => (hQ.2 σ').trans ?_⟩
  rw [hrk]
  have : (0 : ℝ) ≤ large₂.sc.L := by linarith
  gcongr

theorem noBase : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  intro hC D T h large₂ j hj w hrows hL hr hlast hDF hα σ hσ k
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  letI := inst
  have hT := h.thTot j hj
  obtain ⟨x0, hx0⟩ := dom_nonempty ((T.U j σ).X k)
  have hM : 4 * WeightAlgebra.DF w + 4 ≤ T.Q.l.M := by
    rw [h.pins.2.1.1]
    have e0 : WeightAlgebra.DF w + 2 ≤ D.host.g 0 := le_trans hDF (min_le_left _ _)
    have e1 : WeightAlgebra.DF w + 2 ≤ D.host.g 1 := le_trans hDF (min_le_right _ _)
    nlinarith [Nat.mul_le_mul e0 e1]
  obtain ⟨f, ⟨x, P, hP, hfP⟩, hf0⟩ := GlobalTheory.T.thetaGenerators_noCommonZero_of_chartIndependence hC D T h j hj w hr hlast hM hα σ hσ k x0 hx0
  by_contra hno
  push_neg at hno
  obtain ⟨N, cf, g, hsum⟩ := Submodule.mem_span_set'.1 (mem_span_short D T h large₂ j hj w hrows hL hr P hP)
  choose gi hgi using fun i => (existsUnique_thRule _ _ _ hT x (g i).2.1).exists
  have hlin := (GlobalTheory.T.theta_rules_linear_and_level_congruence hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (wtA w) w.n).1
    x N cf (fun i => (g i : _)) f gi (fun i => (g i).2.1) (by rw [hsum]; exact hP) (by rw [hsum]; exact hfP) hgi
  apply hf0
  have hz : ∀ i, rdU (T.U j σ) (gi i) k x0 = 0 := fun i =>
    hno x (g i) (gi i) (g i).2.1 (g i).2.2 (hgi i) x0 hx0

  rw [hlin, map_sum]
  simp only [LinearMap.map_smulₛₗ, Finset.sum_apply, Pi.smul_apply, hz, smul_zero, Finset.sum_const_zero]

end GlobalTheory.NoBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoBaseComponentShortPolynomialGeneratorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.no_base_component_short_polynomial_generator : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  first | exact @GlobalTheory.NoBase.noBase | exact GlobalTheory.NoBase.noBase | (intros; apply GlobalTheory.NoBase.noBase <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralThetaCombinationNonzeroOnComponent

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThetaComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

private lemma card_filter_sum_eq_zero_mul_le_pow (N : ℕ) (v : Fin N → Fin N → ℂ) (hv : ∀ c, v c c ≠ 0) (c : Fin N) :
    (Finset.univ.filter (fun n : Fin N → Fin (N + 1) => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0)).card * (N + 1)
      ≤ (N + 1) ^ N := by
  classical
  set S := Finset.univ.filter (fun n : Fin N → Fin (N + 1) => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0) with hS
  have hinj : Set.InjOn (fun p : (Fin N → Fin (N + 1)) × Fin (N + 1) => Function.update p.1 c p.2)
      ((S ×ˢ (Finset.univ : Finset (Fin (N + 1))) : Finset _) : Set _) := by
    rintro ⟨n, k⟩ hn ⟨n', k'⟩ hn' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at hn hn'
    simp only at heq
    have hk : k = k' := by simpa using congrFun heq c
    subst hk
    have hoff : ∀ i, i ≠ c → n i = n' i := by
      intro i hi
      simpa [Function.update_of_ne hi] using congrFun heq i
    have hrest : ∑ i ∈ Finset.univ.erase c, ((n i : ℕ) : ℂ) * v i c =
        ∑ i ∈ Finset.univ.erase c, ((n' i : ℕ) : ℂ) * v i c :=
      Finset.sum_congr rfl (fun i hi => by rw [hoff i (Finset.ne_of_mem_erase hi)])
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at hn hn'
    have hmul : ((n c : ℕ) : ℂ) * v c c = ((n' c : ℕ) : ℂ) * v c c := by
      linear_combination hn - hn' - hrest
    have hc : n c = n' c := Fin.ext (by exact_mod_cast mul_right_cancel₀ (hv c) hmul)
    refine Prod.ext ?_ rfl
    funext i
    by_cases hi : i = c
    · subst hi; exact hc
    · exact hoff i hi
  have hle := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  simpa [Finset.card_product] using hle

theorem exists_box_comb_ne_zero (N : ℕ) (v : Fin N → Fin N → ℂ) (hv : ∀ c, v c c ≠ 0) :
    ∃ n : Fin N → ℕ, (∀ c, n c ≤ N) ∧ ∀ c, ∑ i, (n i : ℂ) * v i c ≠ 0 := by
  classical
  let bad : Fin N → Finset (Fin N → Fin (N + 1)) := fun c =>
    Finset.univ.filter (fun n => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0)
  have hcount : ∑ c, (bad c).card < (N + 1) ^ N := by
    have h3 : (∑ c, (bad c).card) * (N + 1) ≤ N * (N + 1) ^ N := by
      rw [Finset.sum_mul]
      calc ∑ c, (bad c).card * (N + 1) ≤ ∑ _c : Fin N, (N + 1) ^ N :=
            Finset.sum_le_sum (fun c _ => card_filter_sum_eq_zero_mul_le_pow N v hv c)
        _ = N * (N + 1) ^ N := by simp
    by_contra hcon
    have h4 := Nat.mul_le_mul_right (N + 1) (not_lt.mp hcon)
    have hp : 0 < (N + 1) ^ N := pow_pos (Nat.succ_pos N) N
    nlinarith
  have hlt : (Finset.univ.biUnion bad).card < (Finset.univ : Finset (Fin N → Fin (N + 1))).card := by
    have hcard : (Finset.univ : Finset (Fin N → Fin (N + 1))).card = (N + 1) ^ N := by simp
    rw [hcard]
    exact lt_of_le_of_lt Finset.card_biUnion_le hcount
  obtain ⟨n, -, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨fun i => (n i : ℕ), fun c => Nat.lt_succ_iff.mp (n c).isLt, fun c hc => hn ?_⟩
  exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩

theorem exists_mem_Mlat_ne_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (hInt : ThInt X hinj EX w)
    (N : ℕ) (F : Fin N → B.Cusp j w) (hF : ∀ i, F i ∈ X.thAll w) (b : ℝ) (hb : 0 ≤ b)
    (hFi : ∀ σ i, Real.log (B.supN j w σ (F i)) ≤ b) (σ₀ : B.KO →+* ℂ) (ρ : Fin N → B.Cusp j w → ℂ)
    (hadd : ∀ c G G', ρ c (G + G') = ρ c G + ρ c G') (hsmul : ∀ c (a : B.KO) G, ρ c (a • G) = σ₀ a * ρ c G)
    (hne : ∀ c, ρ c (F c) ≠ 0) :
    ∃ th ∈ B.Mlat j w, (∀ c, ρ c th ≠ 0) ∧
      ∀ σ, Real.log (B.supN j w σ th) ≤ 2 * Real.log N + b + lamStar D * w.size := by
  classical
  obtain ⟨n, hnN, hn⟩ := exists_box_comb_ne_zero N (fun i c => ρ c (F i)) hne
  obtain ⟨hs0, hslog⟩ := sOf_ne_zero_and_log_bounds D B hinj EX j w
  set s : 𝓞 B.KO := sOf B hinj EX w with hs
  set G : B.Cusp j w := ∑ i, n i • F i with hG
  have hGmem : G ∈ X.thAll w := Submodule.sum_mem _ (fun i _ => nsmul_mem (hF i) _)
  have hsG : s • G = ((s : B.KO)) • G := (algebraMap_smul B.KO s G).symm
  have hWW : s • G ∈ X.WWc s w := by
    show s • G ∈ (X.thAll w).map (s • (LinearMap.id : B.Cusp j w →ₗ[𝓞 B.KO] B.Cusp j w))
    exact Submodule.mem_map.2 ⟨G, hGmem, by simp⟩
  have hρG : ∀ c, ρ c G = ∑ i, (n i : ℂ) * ρ c (F i) := by
    intro c
    let φ : B.Cusp j w →+ ℂ := AddMonoidHom.mk' (ρ c) (hadd c)
    have hφ : ∀ x, φ x = ρ c x := fun _ => rfl

    rw [hG, ← hφ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_nsmul, hφ, nsmul_eq_mul]
  have hsne : ((s : B.KO)) ≠ 0 := fun h => hs0 (by exact_mod_cast h)
  refine ⟨s • G, hInt hWW, fun c => ?_, fun σ => ?_⟩
  · rw [hsG, hsmul, hρG]
    exact mul_ne_zero ((map_ne_zero σ₀).2 hsne) (hn c)
  · have hb1 := (GlobalTheory.LogSupMultiple.log_supN_bounds D B j w).2.1 σ N n F b hb hnN (fun i => hFi σ i)
    simp only [Nat.cast_smul_eq_nsmul] at hb1
    obtain ⟨hl0, -, -, hlup⟩ := hslog σ
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hbig := (GlobalTheory.LogSupMultiple.log_supN_bounds D B j w).1 σ (s : B.KO) G (lamStar D * w.size)
      (2 * Real.log N + b) (by linarith) hlup hb1 (by linarith) (by linarith)
    rw [hsG]
    linarith

theorem exists_integral_theta_nonzero_on_components : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → WeightAlgebra.DF w + 2 ≤ qq D → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), ThInt (recPJ h j hj) hinj EX w → ∃ th ∈ (recB h.toLawsCore).Mlat j w, (recPJ h j hj).NonZeroComp w th ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ th) ≤ 2 * Real.log (Fintype.card (T.U j T.σ₀).Comp) + (400 * Zb D large₂ + lamStar D) * w.size := by
  intro hC D T h hG large₂ j hj w hpage hL hrw hlast hDF hinj EX hInt
  classical
  have hLP : Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  have hα := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  have hnb := GlobalTheory.T.no_base_component_short_polynomial_generator hC D T h large₂ j hj w hpage hL hrw hLP hDF hα T.σ₀ T.good_σ₀
  choose x P f hP hcoef hrule x' hx' hne using hnb
  have hfth : ∀ k, f k ∈ T.th j w := fun k => ⟨x k, P k, hP k, hrule k⟩
  have hcut : ∀ k, f k ∈ T.C j w := fun k => h.thCusp j hj (wtA w) w.n (dom_wtA w) hLP (f k) (hfth k)
  have hr0 : 0 < D.R.r := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hn0 : 0 < w.n := by omega
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hsupb : ∀ (σ : T.Q.c.F →+* ℂ) k, Real.log (T.Ns j w σ (f k)) ≤ 400 * Zb D large₂ * w.size := by
    intro σ k
    have hA : (0 : ℝ) ≤ absA w := by unfold absA; positivity
    have hℓ : (0 : ℝ) ≤ 140 * D.R.r * large₂.sc.L * absA w :=
      mul_nonneg (mul_nonneg (by positivity) hL0) hA
    have hl1 : l1At σ (P k) ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
      GlobalTheory.LogSupMultiple.le_exp_of_log_le (hcoef k σ) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    have h1 := GlobalTheory.T.log_supNorm_thetaGenerator_le hC D T h hG large₂ j hj w hpage hL hrw hLP (x k) (P k) (hP k) (f k) (hrule k) σ _ hℓ hl1
    have h2 := (GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w 0 hL hn0).1
    linarith
  have hb : (0 : ℝ) ≤ 400 * Zb D large₂ * w.size := by
    have hZ : (0 : ℝ) ≤ Zb D large₂ := by unfold Zb; exact mul_nonneg (by positivity) hL0
    exact mul_nonneg (mul_nonneg (by norm_num) hZ) (by linarith [w.one_le_size])
  have hcutR : ∀ k, f k ∈ cutR T.C j w := by
    intro k
    simp only [Formalism.L2.Pj.cutR]
    exact Submodule.mem_inf.2 ⟨hcut k, (Submodule.mem_iInf _).2 (fun hn => (hn hj).elim)⟩
  let e := Fintype.equivFin (T.U j T.σ₀).Comp
  let Fc : Fin (Fintype.card (T.U j T.σ₀).Comp) → (recB h.toLawsCore).Cusp j w :=
    fun i => ⟨f (e.symm i), hcutR (e.symm i)⟩
  have hmem : ∀ i, Fc i ∈ (recPJ h j hj).thAll w := by
    intro i
    change Fc i ∈ spanIn T.C j w (T.th j w)
    simp only [Formalism.L2.Pj.spanIn]
    exact Submodule.subset_span (hfth (e.symm i))
  have hsupF : ∀ σ i, Real.log ((recB h.toLawsCore).supN j w σ (Fc i)) ≤ 400 * Zb D large₂ * w.size := by
    intro σ i
    simp only [Formalism.L2.Pj.cutN, if_pos hj]
    exact hsupb σ (e.symm i)
  obtain ⟨th, hth, hρ, hsup⟩ := exists_mem_Mlat_ne_zero (recPJ h j hj) hinj EX w hInt _ Fc hmem
    (400 * Zb D large₂ * w.size) hb hsupF T.σ₀
    (fun c G => rdU (T.U j T.σ₀) (G : T.R j) (e.symm c) (x' (e.symm c)))
    (fun c G G' => by simp [map_add (f := _)])
    (fun c a G => by simp [map_smulₛₗ])
    (fun c => hne (e.symm c))
  refine ⟨th, hth, ?_, fun σ => (hsup σ).trans (le_of_eq (by ring))⟩
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.nonzero_divisor_of_connected D T h j hj w th T.σ₀ T.good_σ₀ (fun k => ⟨x' k, hx' k, ?_⟩)
  have key : ∀ k', e.symm (e k) = k' → rdU (T.U j T.σ₀) (th : T.R j) k' (x' k') ≠ 0 := by
    rintro k' rfl
    exact hρ (e k)
  exact key k (e.symm_apply_apply k)

end GlobalTheory.ThetaComb
end
end
end
