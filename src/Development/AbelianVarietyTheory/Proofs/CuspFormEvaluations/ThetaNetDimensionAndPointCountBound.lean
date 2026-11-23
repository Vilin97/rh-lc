module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
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
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetDataExists
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.ReduceModChar

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lieFacAdd : LieFacAddSt := by
  intro E _ _ _ H Dw x a a'
  simp only [Formalism.L2.Pj.lieFac, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  ring

theorem pnormMul : PnormMulSt := by
  intro E _ _ _ r X la la' P Q x hx
  have hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0 := fun τ j h => by
    have h1 := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := fun τ i =>
    norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))
  have key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) =
      ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) *
        ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la' τ i : ℝ) / 2) := fun τ i => by
    rw [← Real.rpow_add (hpos τ i)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [Pi.mul_apply, norm_mul]
  simp only [key, Finset.prod_mul_distrib]
  ring

theorem pnorm_nonneg' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)

theorem supCMul : SupCMulSt := by
  intro E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg
  unfold supC
  rw [lieFacAdd E H Dw x a a', rdU_mul]
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hn hn' k
  rw [hla]
  have hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤
      Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) *
        Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) := by
    unfold Formalism.L2.Pj.supE
    refine iSup_le fun p => ?_
    have e := pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1)
      (rdU (U σ) g p.1) p.2.1 p.2.2
    refine le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p)
      (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))
    rw [← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]
    exact congrArg ENNReal.ofReal e
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE
  rw [ENNReal.toReal_mul] at h1
  unfold Formalism.L2.Pj.supN
  calc lieFac Dw x a * lieFac Dw x a' *
        (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g)).toReal
      ≤ lieFac Dw x a * lieFac Dw x a' * ((Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f)).toReal *
          (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)).toReal) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos (lieFac_pos _ _ _) (lieFac_pos _ _ _)).le
    _ = _ := by ring

theorem recSubMul : RecSubMulSt := by
  intro D T h j hj σ w w' F G H hH
  have hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w F.2
  have hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n := cutR_le T.C j w' G.2
  have hprod : (H : T.R j) = (F : T.R j) * (G : T.R j) := by
    have h1 := congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH
    change (incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ =
      (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1
    rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd] at h1
    simpa [AddMonoidAlgebra.coeff_single] using h1
  show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G
  unfold cutN
  rw [if_pos hj, if_pos hj, if_pos hj]
  unfold Core.Ns
  rw [hprod, wtA_wadd]
  exact supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even
    (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeepSubMulRecAll

section

@[expose] public section

open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem deepSubMul_rec_all : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), EtaleWeightGaps.DeepSubMul (recPJ h j hj) ∧ EtaleWeightGaps.DeepSubMul (recPlus h j hj) ∧ ∀ (j' : ℕ) (ka : WeightFamilies.Wt D j') (Nt : NetData (recB h.toLawsCore) j' ka) (hM : NetMax Nt) (hL : NetLeSup Nt), EtaleWeightGaps.DeepSubMul (B := Nt.Bp hM hL) (PJ.tol2NormAlt _ _ _ _ _ _ (recPlus h j hj)) := by
  intro D T h j hj
  have h0 : EtaleWeightGaps.DeepSubMul (recPJ h j hj) := recSubMul D T h j hj
  have h1 : EtaleWeightGaps.DeepSubMul (recPlus h j hj) := h0
  exact ⟨h0, h1, fun j' ka Nt hM hL => h1⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRelationDegThree

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

namespace GlobalTheory

theorem page_relation_deg_three : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CG AG : ℝ), 1041 ≤ CG → 3 ≤ AG → 1 ≤ Zb D large₂ → 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) := by
  intro D large₂ j ka CG AG hC hA hZ
  have h1 : Zb D large₂ ^ 3 ≤ Zb D large₂ ^ AG := by
    have := Real.rpow_le_rpow_of_exponent_le hZ hA
    rwa [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast] at this
  have h2 : 0 ≤ Real.log ka.size := Real.log_nonneg ka.one_le_size
  have h3 : WeightFamilies.PPv D large₂ CG AG = CG * Zb D large₂ ^ AG := rfl
  have h4 : 0 ≤ Zb D large₂ ^ 3 := by positivity
  rw [h3]
  have h5 : 1041 * Zb D large₂ ^ 3 ≤ CG * Zb D large₂ ^ AG :=
    mul_le_mul hC h1 h4 (by linarith)
  have h6 : 0 ≤ CG * Zb D large₂ ^ AG := le_trans (by positivity) h5
  nlinarith [mul_nonneg h6 h2]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem net_count_dim {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j} (Nt : NetNorms.NetData B j ka)
    (σ : B.KO →+* ℂ) (c : ℝ) (hM : NetNorms.NetMax Nt) (hS : NetNorms.NetSize Nt c) (hI : NetNorms.NetInj Nt σ) :
    Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c ∧ ∀ n : ℕ, n ≤ Module.finrank B.KO (B.Cusp j ka) → Real.log n ≤ c := by
  have hlog16 : ∀ k : ℕ, Real.log (k : ℝ) ≤ Real.log (16 * (k : ℝ)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      exact Real.log_le_log hk' (by linarith)
  have hfirst : Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c := (hlog16 _).trans (hS σ)
  refine ⟨hfirst, ?_⟩
  intro n hn

  have hdim : Module.finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hli := hI _ (Module.finBasis B.KO (B.Cusp j ka)) (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have hle := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hle
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hc : 0 ≤ Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Nt.NN σ)) with h0 | h0
      · rw [h0]
        simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ Fintype.card (Nt.NN σ) := by exact_mod_cast h0
        linarith
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [hS σ]
  · calc Real.log (n : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := by
          apply Real.log_le_log (by exact_mod_cast hnpos)
          exact_mod_cast hn.trans hdim
      _ ≤ c := hfirst

theorem le_finrank_of_shareRd {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 B.KO) (B.Cusp j ka)) (Tn del : ℕ) (hT : WeightFamilies.dimY D j + 1 ≤ Tn)
    (hR : ShareRd (D := D) (j := j) Tn del (X.rk ka N)) : del ≤ Module.finrank B.KO (B.Cusp j ka) := by
  have hpos : 0 < Nat.choose (Tn - 1) (WeightFamilies.dimY D j) := Nat.choose_pos (by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) := by exact_mod_cast hpos
  have hR' : (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ (X.rk ka N : ℝ) := hR
  have hdel0 : (0 : ℝ) ≤ del := by positivity
  have hdel : (del : ℝ) ≤ (X.rk ka N : ℝ) := by nlinarith

  have hrk : X.rk ka N ≤ Module.finrank B.KO (B.Cusp j ka) := Submodule.finrank_le _
  have hdel' : del ≤ X.rk ka N := by exact_mod_cast hdel
  exact hdel'.trans hrk


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem net_at_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hyp, page, _tie, _p13, _frd, r8, _df, ck⟩ := hP
  obtain ⟨hrows, hf⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hyp page ck
  obtain ⟨hParA, hSetC, -, -, -⟩ := hyp
  obtain ⟨_Q, _PT, hSz, -, -⟩ := page
  obtain ⟨hL2, -⟩ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hParA hSz
  obtain ⟨hkn, -, -, -, -, -, -, -, -, hnP, -, -, -, hnV, -, -, -, -, -, h40, -⟩ := hSetC
  have hfr : D.R.r ≤ D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
  have hr : D.R.r ≤ ka.n := by
    rw [hkn, hnV]
    have : D.R.f * D.R.r ≤ 8 * D.R.f * D.R.r := by
      rw [Nat.mul_assoc]
      omega
    omega
  have hZ : 1 ≤ Zb D large₂ := by
    have hf' : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hr' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast r8
    have hfr' : (128 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    show 1 ≤ (D.R.f : ℝ) * D.R.r * large₂.sc.L
    nlinarith
  obtain ⟨Nt, hM, hLe, hS, hI⟩ := GlobalTheory.RunIn.NetAtRecord.netData_exists D T h
    (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ j hj ka hrows hL2 hr hf
  let σ₀ : (recB h.toLawsCore).KO →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ)).toRingHom
  obtain ⟨hcnt, hdim⟩ := net_count_dim Nt σ₀ _ hM hS (hI σ₀)
  have hpg := GlobalTheory.page_relation_deg_three D large₂ j ka 1041 3 le_rfl le_rfl hZ
  refine ⟨Nt, σ₀, hM, hLe, fun σ => (hS σ).trans hpg, hI σ₀, hcnt.trans hpg,
    (GlobalTheory.deepSubMul_rec_all D T h j hj).1, hdim _ le_rfl, ?_⟩
  intro del _hLat hR
  exact hdim _ (le_finrank_of_shareRd (recPJ h j hj) ka _ Tn del (by omega) hR)

end GlobalTheory.RunJoin
end
end
