module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBoundsStatement
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightRestDegreeAfterGapsBoundsStatement
public import Formalism.LocalRingCardinality.HostCls

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceWeightRowGapMulBoundsSize

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodDepth.Gap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

variable {D : D7}

theorem emb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem emb_ne_conj (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_emb {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [emb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (emb_inj h).symm
    simp [emb_ne_conj, this]
  · simp

theorem real_bounds {T Dd G y w η t S S' η' w2 x : ℝ} (hT : 40 * (Dd + 2) ≤ T) (hD : 0 ≤ Dd) (hG : 0 ≤ G)
    (h1 : (T + Dd + 2) * G ≤ y) (h2 : y < (T + Dd + 2) * (G + 1)) (hy1 : w - η ≤ y) (hy2 : y ≤ S + w + η + 1)
    (hTt : T ≤ t) (htη : t ≤ η) (h3 : t * η ≤ w2 / x) (hx : 1 < x) (hw : w2 ≤ w)
    (hS : S ≤ 2 * S') (hS' : 0 ≤ S') (hη : η ≤ 2 * η') :
    (1 - (Dd + 4) / T) * w ≤ T * G ∧ T * G ≤ w + 100 * (S' + η') := by
  have hT0 : 0 < T := by linarith
  have htη0 : 0 < t * η := mul_pos (by linarith) (by linarith)
  have h4 : t * η * x ≤ w2 := (le_div_iff₀ (by linarith)).1 h3
  have h5 : t * η ≤ w := by nlinarith
  constructor
  · have e : (1 - (Dd + 4) / T) * w = (T - Dd - 4) * w / T := by field_simp; ring
    rw [e, div_le_iff₀ hT0]
    have a1 : (T - Dd - 2) * (w - η - (T + Dd + 2)) ≤ (T - Dd - 2) * ((T + Dd + 2) * G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : 0 ≤ (Dd + 2) ^ 2 * G := by positivity
    have a3 : T * η ≤ t * η := mul_le_mul_of_nonneg_right hTt (by linarith)
    have a4 : T * T ≤ t * η := mul_le_mul hTt (by linarith) hT0.le (by linarith)
    have a5 : 0 ≤ (Dd + 2) * η := mul_nonneg (by linarith) (by linarith)
    have a6 : 0 ≤ (Dd + 2) ^ 2 := by positivity
    nlinarith
  · have a1 : 0 ≤ (Dd + 2) * G := by positivity
    nlinarith

theorem le_two_floor {a : ℝ} (h : 1 ≤ a) : a ≤ 2 * (⌊a⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff a).2 h
  have h2 := Nat.lt_floor_add_one a
  linarith

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem gap_kappa (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hv : D.R.k - 2 < D.R.k - 1) (hm : 0 < D.R.m) :
    0 ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ ∧
    ((WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ : ℤ) : ℚ) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ + (D.hc τ).b ⟨0, hm⟩ - 1 := by
  unfold WeightAlgebra.gapZ
  rw [dite_eq_left h2]
  constructor
  · have := (kaR Tp hK j).aPlus_antitone τ (show (⟨D.R.k - 2, h1⟩ : Fin _) ≤ ⟨D.R.k - 2 + 1, h2⟩ from Nat.le_succ _)
    have h3 : (((kaR Tp hK j).aP τ ⟨D.R.k - 2 + 1, h2⟩ : ℕ) : ℤ) ≤ (kaR Tp hK j).aP τ ⟨D.R.k - 2, h1⟩ := by
      exact_mod_cast this
    exact sub_nonneg.2 h3
  · unfold kaR
    rw [kaWt_big D hK _ j hj.1 hj.2, kaWt_big D hK _ j hj.1 hj.2, Int.cast_sub, (hK j hj.1 hj.2 τ).1,
      (hK j hj.1 hj.2 τ).1, DV.aPlusQ_eq, DV.aPlusQ_eq]
    have e0 : D.R.k - 2 + 1 - (D.R.k - 1) = 0 := by omega
    have s1 : DV.sigPar D τ (D.R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ := by
      unfold DV.sigPar; rw [dite_eq_left hv]
    have s2 : DV.sigPar D τ (D.R.k - 2 + 1) = -(D.hc τ).b ⟨0, hm⟩ := by
      unfold DV.sigPar
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 2
      exact Fin.ext e0
    simp only [s1, s2]
    push_cast
    ring

theorem gapW_eq (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (z : RPl D.R)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hk : 2 ≤ D.R.k) :
    gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z =
      (Int.fdiv (WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ + 2) (WeightAlgebra.Tp D j Tp.TO)).toNat := by
  have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
  show wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) - wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) = _
  rw [wtA_emb, wtA_emb, e]
  unfold ext0
  rw [dite_eq_left h1, dite_eq_left h2]
  show ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2, h1⟩ -
    ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2 + 1, h2⟩ = _
  rw [ofGaps_succ _ ⟨D.R.k - 2, h1⟩ h2, Nat.add_sub_cancel]
  unfold lGapP
  rw [if_pos h2]

theorem TO_le_t (Tp : ParamsT D L Pm) : Tp.TO ≤ D.R.t := by
  have a1 := Tp.split
  have a2 := Tp.nP_eq
  have a4 := Tp.nW_40
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.toFrame.ord := D.R.toFrame.ord_pos
    have h1 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have a5 : Tp.TO * 1 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ (by omega)
  have a6 : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
  omega

theorem gap_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  intro D L Pm Tp hK j hj z hw
  have hj1 := hj.1
  have hj2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 : D.R.k - 2 < (D.R.sigW j).1 := by omega
  have h2 : D.R.k - 2 + 1 < (D.R.sigW j).1 := by omega
  have hv : D.R.k - 2 < D.R.k - 1 := by omega
  have hm : 0 < D.R.m := by omega
  have hjm : j - 1 < D.R.m := by omega
  rw [gapW_eq Tp hK z h1 h2 (by omega)]
  obtain ⟨g0, g1⟩ := gap_kappa Tp hK hj (plOf D z) h1 h2 hv hm
  generalize WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ = c at g0 g1 ⊢
  have hT' : WeightAlgebra.Tp D j Tp.TO = Tp.TO + Tp.Dp + 2 := by
    unfold WeightAlgebra.Tp; rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
  rw [hT', Int.fdiv_eq_ediv_of_nonneg _ (Nat.cast_nonneg _)]
  have hpos : (0 : ℤ) < ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := by positivity
  have q0 : 0 ≤ (c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) hpos.le
  have q1 := Int.mul_ediv_self_le (x := c + 2) hpos.ne'
  have q2 := Int.lt_mul_ediv_self_add (x := c + 2) hpos
  have q3 := Int.toNat_of_nonneg q0
  generalize ((c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)).toNat = G at q3 ⊢
  rw [← q3] at q1 q2
  have r1 : ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) ≤ (c : ℝ) + 2 := by exact_mod_cast q1
  have r2 : (c : ℝ) + 2 < ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) + ((Tp.TO : ℝ) + Tp.Dp + 2) := by exact_mod_cast q2
  have g2 : (c : ℝ) = (((D.hc (plOf D z)).v ⟨D.R.k - 2, hv⟩ : ℚ) : ℝ) + (((D.hc (plOf D z)).b ⟨0, hm⟩ : ℚ) : ℝ) - 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) g1
  have hwe : (numOf D L).w j z = (((D.hc (plOf D z)).e ⟨j - 1, hjm⟩ : ℚ) : ℝ) := by
    unfold NumDatum.w NumDatum.eQ
    congr 1
    split_ifs with h
    · rfl
    · exact absurd (by first | exact hjm | exact ⟨hj1, hj2⟩) h
  have c1 := L.cloud_v (plOf D z) ⟨D.R.k - 2, hv⟩
  have c2 := abs_le.1 (L.be_close (plOf D z) ⟨0, hm⟩ ⟨j - 1, hjm⟩)
  rw [Rat.cast_sub] at c2
  have hT40 : 40 * ((Tp.Dp : ℝ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have hD : (0 : ℝ) ≤ Tp.Dp := Nat.cast_nonneg _
  have hT2 : (1 : ℝ) ≤ (Tp.TO : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hDel := le_two_floor (hT2.trans Tp.Del_TO)
  have hh0 : (1 : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hh := le_two_floor hh0
  have hmR : (0 : ℝ) < D.R.m := by exact_mod_cast hm
  refine real_bounds (y := (c : ℝ) + 2) (η := L.etaSz) (t := D.R.t) (S := L.Sc) hT40 hD (Nat.cast_nonneg _) r1
    (by linarith) (by rw [hwe]; linarith [c1.1, c2.1]) (by rw [hwe]; linarith [c1.2, c2.2])
    (by exact_mod_cast TO_le_t Tp) Pm.t_le_eta Pm.teta L.sc.one_lt_alt hw ?_ ?_ ?_
  · rw [L.Sc_eq]
    show _ ≤ 2 * ((D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)))
    have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    nlinarith
  · unfold NumDatum.Sc; positivity
  · show _ ≤ 2 * ((D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ))
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    rw [e]
    nlinarith

end GlobalTheory.GoodDepth.Gap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceWeightRowGapMulBoundsSizeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  first | exact @GlobalTheory.GoodDepth.Gap.gap_bounds | exact GlobalTheory.GoodDepth.Gap.gap_bounds | (intros; apply GlobalTheory.GoodDepth.Gap.gap_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParameters

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem goodPage_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  intro D L Pm Tp hK T hP hC h5 hx hkb hlog j hj
  obtain ⟨hfirst, hw⟩ := GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK j hj hx hkb
  obtain ⟨hr0, hr1⟩ := GlobalTheory.T.weight_rest_degree_after_gaps_bounds D L Pm Tp hK T hP j hj
  have hgap := fun z => GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size D L Pm Tp hK j hj z (hw z).1
  have hj1 : 1 ≤ j := hj.1
  have hj2 : j ≤ D.R.m := hj.2
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hn : 0 < D.R.n := by unfold Ranks.n; have := D.R.m_le_f; omega
  have hf : 1 ≤ D.R.f := by unfold Ranks.f; omega
  have hr : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hDp : 1 ≤ Tp.Dp := by
    rw [Tp.Dp_eq]
    exact Nat.mul_pos hf (Nat.choose_pos hr)
  have h40 := Tp.TO_40
  have hTpos : (0 : ℝ) < Tp.TO := by exact_mod_cast TO_pos Tp
  have hx0 : 0 < L.sc.x := by linarith
  have hw'' : 0 < L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b Scale.X'
    have : (0 : ℝ) < D.R.n := by exact_mod_cast hn
    positivity
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hwj : ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
    intro z
    have h1 : j - 1 < D.R.m := by omega
    have h2 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := ⟨hj1, hj2⟩
    unfold NumDatum.w NumDatum.eQ wj
    rw [dite_eq_left h1, dite_eq_left h2]
    rfl
  refine ⟨⟨((Tp.Dp : ℝ) + 4) / Tp.TO, ?_, fun z => lt_of_lt_of_le hw'' (hw z).1, fun z => (hgap z).1,
    fun z => (hgap z).2, ⟨by positivity, ?_⟩, ?_, hr0, hr1⟩, fun τ _ => hfirst τ, ?_, ?_, hlog, ?_, ?_⟩
  · exact_mod_cast TO_pos Tp
  · rw [div_le_one hTpos]
    exact_mod_cast (by omega : Tp.Dp + 4 ≤ Tp.TO)
  · show ((D.R.k : ℝ) - 1) * (((Tp.Dp : ℝ) + 4) / Tp.TO) ≤ 5 * D.R.m
    have h := Tp.TO_Dk
    rw [div_le_iff₀ hm0] at h
    rw [← mul_div_assoc, div_le_iff₀ hTpos]
    have hD : (1 : ℝ) ≤ Tp.Dp := by exact_mod_cast hDp
    have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    nlinarith [mul_nonneg (sub_nonneg.2 hD) (sub_nonneg.2 hk)]
  · refine le_trans ?_ Tp.nW_win.1
    show 10 * (D.R.r : ℝ) * (D.R.f + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤ _
    unfold LevelStarExponents.nW
    have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      linarith
    gcongr
  · refine le_trans h5 ?_
    unfold Scale.L
    have := L.sc.eps_pos
    have := L.sc.ez_le
    exact Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)
  · intro p hp hin
    by_contra h
    have hin' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := hin
    have hne2 : p ≠ 2 := by
      rintro rfl
      have e : D.host.cls 2 = PrimeClass.ram2 := primeClass_two D.host.toHostRaw
      rw [e] at hin'
      simp at hin'
    have hp3 : p = 3 := by
      have h5 : p < 5 := not_le.1 h
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hne2
      · rfl
      · exact absurd hp (by norm_num)
    have hp4 : p ≤ D.host.splitBound := by
      rw [hp3]
      exact le_trans (Nat.le_floor (by exact_mod_cast h5)) L.split_tie
    have hjac := D.host.split_small p hp hne2 hp4
    rcases hin' with e | e
    · exact ((primeClass_eq_inert_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
    · exact ((primeClass_eq_signal_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
  · intro z z'
    rw [hwj, hwj]
    exact Pm.X''_ratio j j _ _ hj1 hj2 hj1 hj2

end GlobalTheory.GoodDepth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParametersStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  first | exact @GlobalTheory.GoodDepth.goodPage_run | exact GlobalTheory.GoodDepth.goodPage_run | (intros; apply GlobalTheory.GoodDepth.goodPage_run <;> assumption)
end
end
