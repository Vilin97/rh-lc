module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraicStatement
import Formalism.LocalToGlobal.ProjectiveLattices.PhiSetPullSub
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
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBoundsStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductFormValuationBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaVal

theorem two_mul_le_of_card_div_le {N i : ℕ} {a p p' : ℝ} {v : EReal} (hN : N = 2 * 5 ^ 4 * i) (hp : p = p')
    (hv : (((N : ℝ) / ((5 : ℕ) : ℝ) ^ 4 * (a * p') : ℝ) : EReal) ≤ v) : ((2 * i * (a * p) : ℝ) : EReal) ≤ v := by
  have h5 : (N : ℝ) / ((5 : ℕ) : ℝ) ^ 4 = 2 * i := by
    rw [hN]; push_cast; ring
  rw [h5, ← hp] at hv
  exact hv

theorem val_at_partner {D : D7} {Q : Par D} (G : In66 Q) (hT : G.PinTower) (hL : G.PinLat) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j < D.R.m) (i : ℕ) (f : Rul (Q.Xo j) Q.c) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ)
    (xs : J → Fin n → LatMod (Q.Dw j) (5 ^ 4)) (hcard : Nat.card (LevGrp (Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i)
    (hsp : Spans xs) (hrule : IsEtaRule (Q.Xo j) Q.c 5 cf xs f) (la : HeightOneSpectrum (𝓞 Q.c.F))
    (y : PtV (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (G.PY j (WeightAlgebra.resCh la)) (G.lies j la) la) :
    ((2 * i * ((eWL Q.c.F la : ℝ) * (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).phiCy (imgV y)) : ℝ) : EReal) ≤ vAtV y f := by
  obtain ⟨S, io, e, ho, y', hy, eta, hl, hq⟩ := y.2
  have hi : imgV y = eta := congrArg Prod.snd hq
  have hf : vAtV y f = nval S.V e (evI y' f) := congrFun (congrArg Prod.fst hq) f
  rw [hi, hf]
  obtain ⟨z, hr, hz⟩ := hl h2
  obtain ⟨A, bA, hb, hv⟩ := GlobalTheory.T.phiC_le_normalized_valuation_product_form_algebraic D.host.E _ (Q.Dw j) _ (Q.Xo j) Q.c la
    (G.Tw j (WeightAlgebra.resCh la)) (hT j h1 h2 _ (resCh_prime la)) S io e y' z ho hy hz
    (fun x : D.host.E => D.host.conj x) (fun a => by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj]
      exact WeightFamilies.emb_conj D _ a)
  have hphi := In66.phiCy_eq G hL h1 h2 ⟨S, io, e, y', ho, hy, hz⟩ hr A bA hb
  have key := hv 5 (by decide) (by norm_num) J n cf xs f hsp hrule
  exact two_mul_le_of_card_div_le hcard hphi key

theorem recPJ_phiC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (h2 : j < D.R.m)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) :
    (recPJ h j hj).phiC la y =
      (eWL T.Q.c.F la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy (imgV y) := by
  unfold WeightAlgebra.PJ.phiC
  rw [if_pos h2]
  rfl

theorem etVal_of_isEtaRule : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod (T.Q.Dw j) (5 ^ 4)), Nat.card (LevGrp (T.Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i → Spans xs → IsEtaRule (T.Q.Xo j) T.Q.c 5 cf xs η.1 → EtVal h j ⟨h1, h2.le⟩ i η := by
  intro D T h j h1 h2 i η J _ n cf xs hcard hsp hrule la y
  have e1 := recPJ_vAt_inc h j ⟨h1, h2.le⟩ la y _ η
  have e2 := recPJ_phiC h ⟨h1, h2.le⟩ h2 la y
  have key := val_at_partner T.G h.tower h.lattice_condition h1 h2 i η.1 J n cf xs hcard hsp hrule la y
  rw [← e2, ← e1] at key
  exact key

end GlobalTheory.EtaVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductFormValuationBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

theorem _root_.GlobalTheory.T.etaProductForm_valuation_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod (T.Q.Dw j) (5 ^ 4)), Nat.card (LevGrp (T.Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i → Spans xs → IsEtaRule (T.Q.Xo j) T.Q.c 5 cf xs η.1 → EtVal h j ⟨h1, h2.le⟩ i η := by
  first | exact @GlobalTheory.EtaVal.etVal_of_isEtaRule | exact GlobalTheory.EtaVal.etVal_of_isEtaRule | (intros; apply GlobalTheory.EtaVal.etVal_of_isEtaRule <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstant

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem wtA_wEt_eq_zero (D : D7) (j i : ℕ) : wtA (wEt D j i) = 0 := by
  funext x
  simp [wtA, wEt, WeightAlgebra.wscalar, Formalism.L2.Pj.ext0]

theorem exists_form_four_clauses (D : D7) (T : Top D) (h : LawsP T) (DF q : ℕ) (R0 P tableLineDegreeTwo : ℝ)
    (hrun : RunOK D.host.E D.R.r DF q R0 D.R.m)
    (hp : ∀ j, InR D j → p16 D.host.E D.R.r q D.R.m 5
      (max 1 (Fintype.card (T.U j T.σ₀).Comp) * 5 ^ (8 * I2.PT.f D.host.E * D.R.r ^ 2)) ≤ min P tableLineDegreeTwo)
    (hP : 0 ≤ P) : ETEx h P (EtArch h (I2.th (E := D.host.E) q R0) tableLineDegreeTwo) := by
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  have hdat := h.pins.2.2.2 j hj
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [hdat.2.1]; simp [Ranks.sigW]
  have hr : 2 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  obtain ⟨i, J, fJ, cf, xs, f, hi, hcard, hsp, hrule, hcusp, hne, -, hnzd, harch, hsup⟩ :=
    GlobalTheory.T.exists_product_cuspForm_ne_zero_arch_supNorm_bounds D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ (fun σ hσ => h.unf j hj σ hσ) T.good_σ₀
      (h.allTest j hj) hr 5 (by decide) (by norm_num) DF q D.R.m R0 hrun (Or.inr hq)
  have hw := wtA_wEt_eq_zero D j i
  have hn : (wEt D j i).n = 2 * 5 ^ 4 * D.R.r * i := rfl
  have hmemC : f ∈ T.C j (wEt D j i) := by
    change f ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (wEt D j i)) (wEt D j i).n
    rw [hw, hn]; exact hcusp
  have hmem : f ∈ cutR T.C j (wEt D j i) := by rw [cutR_eq T.C hj]; exact hmemC
  have hpj := hp j hj
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  refine ⟨i, hi, ⟨f, hmem⟩, ⟨fun h0 => hne (congrArg Subtype.val h0), ?_⟩, ?_, ?_, ?_⟩
  · intro w' G hFG
    have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
    have hm : f * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd (wEt D j i) w') := by
      rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj _ w' _ hmemC _ hGc
    have hval : f * (G : T.R j) = 0 := by
      have e1 : incG deg (cutR T.C j) (wEt D j i) ⟨f, hmem⟩ * incG deg (cutR T.C j) w' G = 0 := hFG
      rw [incG_mul deg (cutR T.C j) (deg_wadd (wEt D j i) w') ⟨f, hmem⟩ G hm] at e1
      have e2 := incG_inj deg (cutR T.C j) _ (e1.trans (map_zero _).symm)
      exact congrArg Subtype.val e2
    exact Subtype.ext (hnzd _ _ _ (dom_wtA w') (cusp_le_sec _ _ _ _ _ hGc) hval)
  · exact GlobalTheory.T.etaProductForm_valuation_bound D T h j h1 h2 i ⟨f, hmem⟩ J D.R.r cf xs hcard hsp hrule
  · intro σ
    have e : (recB h.toLawsCore).supN j _ σ ⟨f, hmem⟩ =
        supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) 0 (2 * 5 ^ 4 * D.R.r * i) f := by
      change cutN T.C T.Ns j (wEt D j i) σ ⟨f, hmem⟩ = _
      unfold cutN
      rw [if_pos hj]
      unfold Core.Ns
      rw [hw, hn]
    have hs0 := (recB h.toLawsCore).supN_nonneg j _ σ ⟨f, hmem⟩
    have hb := hsup (goodOf T.Q.c σ) (xiR D) (goodEmb_goodOf _ σ)
    have hb' : (recB h.toLawsCore).supN j _ σ ⟨f, hmem⟩ ≤ Real.exp (i * P) := by
      rw [e]
      refine le_trans hb (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_left (hpj.trans (min_le_left _ _)) hi'.le
    rw [div_le_iff₀ hi', mul_comm]
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; positivity
    · exact (Real.log_le_iff_le_exp h0).mpr hb'
  · intro σ hσ k x hx
    have hb := harch σ hσ k x hx
    have hl : lieFac (T.Q.Dw j) (xiR D) 0 = 1 := by simp [lieFac]
    rw [hw, hn, hl, one_mul]
    refine le_trans hb (Real.exp_le_exp.mpr ?_)
    have := hpj.trans (min_le_right _ _)
    refine mul_le_mul_of_nonpos_left ?_ (by linarith)
    exact sub_le_sub_left this _

end GlobalTheory.EtaAn
end
end
