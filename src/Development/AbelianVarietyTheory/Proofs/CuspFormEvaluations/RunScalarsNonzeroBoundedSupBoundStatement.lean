module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFiniteSpanningShortGeneratorsSmallSupNorm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBounded
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBoundedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.runScalars_ne_zero_and_log_bounded : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  first | exact @GlobalTheory.RunIn.scalOfP_size | exact GlobalTheory.RunIn.scalOfP_size | (intros; apply GlobalTheory.RunIn.scalOfP_size <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLattice

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem span_image_smul_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (c : K) (hc : c ≠ 0)
    (S : Set V) (hS : Submodule.span K S = ⊤) : Submodule.span K ((fun g => c • g) '' S) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have key : ∀ x ∈ Submodule.span K S, c • x ∈ Submodule.span K ((fun g => c • g) '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul e x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ e hx
  have hv : c⁻¹ • v ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  simpa [smul_smul, hc] using key _ hv

theorem shortG_scaled : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  intro D B P j X w s Sh a b hs ha hb hsa hSh hspan
  classical

  let N : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * w.n
  let t : 𝓞 B.KO := s * (N : 𝓞 B.KO) ^ k
  have hN1 : (1 : ℝ) ≤ N := by
    have h0 := (D.host.g_prime 0).one_lt
    have h1 := (D.host.g_prime 1).one_lt
    have : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have htK : ((t : 𝓞 B.KO) : B.KO) = (s : B.KO) * ((N : ℕ) : B.KO) ^ k := by
    simp [t]
  have hsK : (s : B.KO) ≠ 0 := fun h => hs (by exact_mod_cast h)
  have hNK : ((N : ℕ) : B.KO) ≠ 0 := by
    have : N ≠ 0 := by
      intro h; rw [h] at hN1; norm_num at hN1
    exact_mod_cast this
  have ht0 : ((t : 𝓞 B.KO) : B.KO) ≠ 0 := by
    rw [htK]; exact mul_ne_zero hsK (pow_ne_zero _ hNK)
  have hsm : ∀ g : B.Cusp j w, t • g = ((t : 𝓞 B.KO) : B.KO) • g := fun g =>
    (algebraMap_smul B.KO t g).symm
  have hlam : 0 ≤ Real.log N ∧ Real.log N ≤ lamStar D := by
    have h2 := (pPow_size D j w).2.2.1
    refine ⟨Real.log_nonneg hN1, ?_⟩
    unfold Formalism.MainNotions.WeightAlgebra.lamStar
    have : ((N : ℕ) : ℝ) = (D.host.g 0 : ℝ) * D.host.g 1 := by simp [N]
    rw [← this]; linarith
  have hk : (k : ℝ) ≤ w.size := by
    unfold WeightFamilies.Wt.size
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hsum : 0 ≤ ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by positivity
    have : (k : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      calc (k : ℝ) = (D.R.f : ℝ) * 1 * (D.R.r : ℝ) * (w.n : ℝ) := by simp [k]
        _ ≤ _ := by gcongr
    linarith
  refine ⟨Sh.image fun g => t • g, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [PJ.Thc, PJ.scaled]
    refine Submodule.mem_map.mpr ⟨((N : 𝓞 B.KO) ^ k) • g, Submodule.mem_map.mpr ⟨g, (hSh g hg).1, by simp [N, k]⟩, ?_⟩
    simp only [t, mul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  · have : ((Sh.image fun g => t • g : Finset (B.Cusp j w)) : Set (B.Cusp j w)) =
        (fun g => ((t : 𝓞 B.KO) : B.KO) • g) '' (Sh : Set (B.Cusp j w)) := by
      rw [Finset.coe_image]
      exact congrArg (· '' (Sh : Set (B.Cusp j w))) (funext hsm)
    rw [this]
    exact span_image_smul_top _ ht0 _ hspan
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    apply WeightFamilies.meanLogSup_le
    intro σ
    rw [hsm, B.supN_smul, htK]
    have hσs : 0 < ‖σ (s : B.KO)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hsK)
    have hnorm : ‖σ ((s : B.KO) * ((N : ℕ) : B.KO) ^ k)‖ = ‖σ (s : B.KO)‖ * (N : ℝ) ^ k := by
      simp
    rw [hnorm]
    have hlog_s := hsa σ
    have hG := (hSh g hg).2 σ
    have hkN : (k : ℝ) * Real.log N ≤ lamStar D * w.size := by
      calc (k : ℝ) * Real.log N ≤ w.size * Real.log N := mul_le_mul_of_nonneg_right hk hlam.1
        _ ≤ w.size * lamStar D :=
            mul_le_mul_of_nonneg_left hlam.2 (by linarith [WeightFamilies.Wt.one_le_size w])
        _ = lamStar D * w.size := mul_comm _ _
    by_cases hg0 : B.supN j w σ g = 0
    · rw [hg0, mul_zero, Real.log_zero]
      have : 0 ≤ lamStar D * w.size :=
        mul_nonneg (hlam.1.trans hlam.2) (by linarith [WeightFamilies.Wt.one_le_size w])
      linarith
    · have hNk : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (by linarith) _
      rw [Real.log_mul (mul_pos hσs hNk).ne' hg0, Real.log_mul hσs.ne' hNk.ne', Real.log_pow]
      linarith

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.shortGenerators_scaled_thetaLattice : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  first | exact @GlobalTheory.RunIn.shortG_scaled | exact GlobalTheory.RunIn.shortG_scaled | (intros; apply GlobalTheory.RunIn.shortG_scaled <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem scalB_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  intro hCI D T h hGam hSh hA hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hHP hRows hSpF hSpF0 hSpK
  obtain ⟨-, hSet, -, -, -⟩ := id hHP
  obtain ⟨hkaN, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hIsL, hIsF, -, -, -, -, -, h40, -, -, -, -⟩ := hSet
  have hLn : wL.n = nW := hIsL.1
  have hkn : ka.n = nP + Tn * nW := hkaN.trans hnV
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    · exact D.host.pde_prime.pos
    · exact D.host.pde'_prime.pos
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hHP
  have hsz := GlobalTheory.T.runScalars_ne_zero_and_log_bounded D (recB h.toLawsCore) hinj EX j p ka wL wF Tn nP nW hp0 (by omega) hLn hIsF hkn
  have hsW := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hWeq := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)

  have hW : ∀ w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w ∧ D.R.r ≤ w.n ∧ w.LastPos := by
    intro w hw
    obtain ⟨hdf, hn, hr, hlast⟩ := hwb.1 w hw
    exact ⟨GlobalTheory.pageRows_of_le D large₂ j ka w (by linarith) hdf hn hRows, hr, hlast⟩

  have hShort : ∀ (w : WeightFamilies.Wt D j) (s : 𝓞 (recB h.toLawsCore).KO) (c : ℝ),
      w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → s ≠ 0 → 0 ≤ c →
      c ≤ 2 * (lamStar D + 2 * Real.log p) * w.size →
      (∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ (s : (recB h.toLawsCore).KO)‖ ≤ c) →
      ShortG (recPJ h j hj) w ((recPJ h j hj).Thc s w) (Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) p * w.size) := by
    intro w s c hw hsp hs hc0 hc hsc
    obtain ⟨hRw, hrw, hlw⟩ := hW w hw
    have hn8 : 0 < w.n := by omega
    obtain ⟨Sh, hSh1, hSh2⟩ := GlobalTheory.RunIn.exists_short_family_small hCI D T h hGam large₂ j hj w hRw hL2 hrw hlw hSh (hA j hj w.n) hsp
    have hsize : 1 ≤ w.size := WeightFamilies.Wt.one_le_size w
    have key := GlobalTheory.T.shortGenerators_scaled_thetaLattice D _ _ j (recPJ h j hj) w s Sh c (400 * Zb D large₂ * w.size) hs hc0
      (mul_nonneg (by linarith) (by linarith)) hsc hSh1 hSh2
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w p hL2 hn8).2.1
    unfold ShortG at key ⊢
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := key
    exact ⟨S', hS'1, hS'2, fun g hg => (hS'3 g hg).trans (by nlinarith)⟩
  unfold ScalB
  refine ⟨hWeq ▸ hsW.1, hsz.1, hsz.2.1, hsz.2.2.1, fun σ => ?_, p, (Formalism.MainNotions.Gaps.FamilyHypotheses.ownPr_iff D p).1 hp,
    fun σ => hsz.2.2.2 σ, 1009 * Zb D large₂, le_rfl, ?_⟩
  · rw [hWeq]
    exact ⟨(hsW.2 σ).1, (hsW.2 σ).2.1⟩
  unfold S4
  have hsizeL : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hRL, hrL, hlL⟩ := hW wL (by simp)
    have hnL : 0 < wL.n := by omega
    obtain ⟨N, w0, hspan, -, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hCI D T h hGam large₂ j hj wL hRL hL2 hrL hlL
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL p hL2 hnL).2.2
    have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
      rw [Real.log_abs]
      exact Real.log_intCast_nonneg _
    have hb : 0 ≤ 400 * Zb D large₂ * wL.size + 3 * D.R.f * D.R.r * wL.n * large₂.sc.L +
        5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) +
        Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
      have h1 : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ (3 * D.R.f * D.R.r * wL.n : ℝ) * large₂.sc.L := mul_nonneg (by positivity) (by linarith)
      have h3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO :=
        div_nonneg hdisc (by positivity)
      have h4 : 0 ≤ 400 * Zb D large₂ * wL.size := mul_nonneg (by linarith) (by linarith)
      linarith
    exact (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF _ N w0 _ _ _ 0
      (mul_nonneg (by linarith) (by linarith)) hb (fun σ => (hsz.2.2.2 σ).1) hspan hsup hG).1
  · have hsF : ∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sF : (recB h.toLawsCore).KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size :=
      fun σ => (hsz.2.2.2 σ).2.1
    exact hShort wF _ _ (by simp) hSpF hsz.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size wF])) (by nlinarith [WeightFamilies.Wt.one_le_size wF]) hsF
  · exact hShort _ _ _ (by simp) hSpF0 hsz.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ((recPJ h j hj).wF0 wL wF)])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.1)
  · exact hShort ka _ _ (by simp) hSpK hsz.2.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ka])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.2)

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.runScalars_nonzero_bounded_supBound : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  first | exact @GlobalTheory.RunIn.scalB_rec | exact GlobalTheory.RunIn.scalB_rec | (intros; apply GlobalTheory.RunIn.scalB_rec <;> assumption)
end
end
