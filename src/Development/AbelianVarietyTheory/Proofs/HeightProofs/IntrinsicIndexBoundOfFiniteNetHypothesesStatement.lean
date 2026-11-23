module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Formalism.LocalToGlobal.ProjectiveLattices.XPlusWireT
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNormStatement
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.DeepSubMulSecNorm

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (n : SecNorm B)




theorem hypC_secNorm (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) H C2 A2 CR Bx CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S)
        ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl




theorem deepSubMul_secNorm : DeepSubMul (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ↔ DeepSubMul X := Iff.rfl

end




theorem baseIn_secNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B), BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → BaseIn large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨(hypC_secNorm X n large₂ H C2 A2 CR 0 CT S ka wL wF Tn nP nW h0 nus).2 a1,
    (latAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4).2 a2,
    (lamwAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ K.CL K.AL).2 a3,
    fun hj => (qAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ _ _ _ _ _ _ _ _).2 (a4 hj),
    (deepSubMul_secNorm X n).2 a5⟩

end GlobalTheory.FinalJoin
end
end

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

namespace NetData

variable (Nt : NetData B j ka)

theorem inner_euclideanEmbedding_eq_average (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) =
      (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ y, conj (Nt.ev σ y F) * Nt.ev σ y G := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
  · have hc : (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) = ((Nt.cf σ : ℝ) : ℂ) * ((Nt.cf σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Nt.cf_sq]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Nt.goodRowsProjector_apply_eq_sum, if_true, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  · intro τ _ h
    simp [Nt.goodRowsProjector_apply_eq_sum, h]
  · simp

def herm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => Nt.netN σ) (Fintype.card (Σ τ : B.KO →+* ℂ, Nt.NN τ)) where
  e σ := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ τ : B.KO →+* ℂ, Nt.NN τ))).toLinearEquiv.toLinearMap.comp
    (Nt.e0 σ)
  norm_e σ F := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, Nt.norm_euclideanEmbedding_eq_netNorm]

theorem herm_inner (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.herm.e σ F) (Nt.herm.e σ G) = inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) := by
  simp only [herm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

theorem herm_conj : Nt.herm.Conj := by
  intro σ f g
  rw [Nt.herm_inner, Nt.herm_inner, Nt.inner_euclideanEmbedding_eq_average, Nt.inner_euclideanEmbedding_eq_average]
  rw [← Fintype.card_congr (Nt.cj σ), ← (Nt.cj σ).sum_comp]

  simp only [Nt.ev_conj, Complex.conj_conj, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, map_mul]

end NetData

theorem sup_L2_bound_of_net : SupL2BoundFromNet (D := D) (B := B) (j := j) (ka := ka) := by
  intro Nt hM hL large₂ CG AG hP F σ
  rw [Nt.Bp_L2N_run hM hL]
  change B.supN j ka σ F ^ 2 ≤ _ * Nt.netN σ F ^ 2
  obtain ⟨y, hy⟩ := hM σ F
  have hS := B.supN_nonneg j ka σ F
  have hn : (1 : ℝ) ≤ (Fintype.card (Nt.NN σ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨y⟩).ne'
  have hsum0 : (0 : ℝ) ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Nt.netN σ F ^ 2 = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by linarith)) hsum0)
  have h1 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : (B.supN j ka σ F / 4) ^ 2 ≤ ‖Nt.ev σ y F‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  have h3 : B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := by
    rw [hsq]
    have : 16 * (Fintype.card (Nt.NN σ) : ℝ) * ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2) =
        16 * ∑ y, ‖Nt.ev σ y F‖ ^ 2 := by
      field_simp
    rw [this]
    have h4 : (B.supN j ka σ F / 4) ^ 2 = B.supN j ka σ F ^ 2 / 16 := by ring
    linarith
  have h4 : 16 * (Fintype.card (Nt.NN σ) : ℝ) ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * (Fintype.card (Nt.NN σ) : ℝ))]
    exact Real.exp_le_exp.mpr (hP σ)
  calc B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := h3
    _ ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * Nt.netN σ F ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

theorem deepHermNet : DeepHermNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X
  exact ⟨_, { e := Nt.herm.e, norm_e := fun σ F => (Nt.herm.norm_e σ F).trans (by rw [Nt.Bp_L2N_run hM hL]) },
    Nt.herm_conj⟩

theorem deepLogDNet : DeepLogDNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X σ Pd hI hP
  change Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd
  have hd : finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hb := hI _ _ (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have := hb.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hlog0 : 0 ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos (finrank B.KO (B.Cusp j ka)) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · calc Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hd)
      _ ≤ Pd := hP

end Formalism.MainNotions.Gaps.NetNorms
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.SecNormOfNetIn

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem secNorm_of_netIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (ka : WeightFamilies.Wt D j) (Pd : ℝ), NetIn large₂ B j ka K Pd → ∃ n : SecNorm B, SupBoundByL2AtWeight large₂ n.base j ka K.CG K.AG ∧ DeepHerm (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka ∧ DeepLogD (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka Pd := by
  intro D B P j X large₂ K ka Pd h
  obtain ⟨Nt, σ₀, hM, hL, hP, hI, hd⟩ := h
  refine ⟨⟨(Nt.Bp hM hL).l2NormAlt, (Nt.Bp hM hL).l2Norm_nonneg_bis, (Nt.Bp hM hL).l2Norm_eq_zero_iff, (Nt.Bp hM hL).l2Norm_smul_alt,
    (Nt.Bp hM hL).l2Norm_add_le', (Nt.Bp hM hL).l2Norm_le_supNorm_alt⟩, NetNorms.sup_L2_bound_of_net Nt hM hL large₂ _ _ hP, ?_, ?_⟩
  · exact NetNorms.deepHermNet P Nt hM hL _
  · exact NetNorms.deepLogDNet P Nt hM hL (PJ.tol2NormAlt _ _ _ _ _ _ X) σ₀ Pd hI hd

end GlobalTheory.FinalJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypotheses

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin




theorem inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨hB, G, Gc, PH, Prw, Pet, Pd, hN, hF, hP⟩ := h
  obtain ⟨n, h1, h2, h3⟩ := secNorm_of_netIn D B P j X large₂ K ka Pd hN
  obtain ⟨G', hF', hP'⟩ := GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n G Gc PH Prw Pet
    Pd _ hF hP
  exact ⟨n, baseIn_secNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n hB, h1, h2,
    G', Gc, PH, Prw, Pet, Pd, h3, hF', hP'⟩

end GlobalTheory.FinalJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypothesesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.exists_secNorm_inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_of_inputsNet | exact GlobalTheory.FinalJoin.inputsR_of_inputsNet | (intros; apply GlobalTheory.FinalJoin.inputsR_of_inputsNet <;> assumption)
end
end
