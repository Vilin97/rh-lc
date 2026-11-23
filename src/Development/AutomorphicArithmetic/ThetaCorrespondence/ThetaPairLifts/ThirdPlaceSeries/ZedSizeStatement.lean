module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SevenMulHeightBoundLeHalfOfParametersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubProdLeSumOfLe
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntRCloudSub
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeDefectLeOfDividedWeight

section

@[expose] public section

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem vdm_cast_eq_range {ι : Type} [Fintype ι] {N : ℕ} (la : ι → Fin N → ℤ) (v : ι → ℕ → ℝ)
    (hv : ∀ τ (i : Fin N), v τ i = la τ i) :
    ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l) := by
  rw [show ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = _ from GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) la]
  unfold GlobalTheory.CompHt.vdm
  refine Finset.prod_congr rfl fun τ _ => ?_
  have lhs : ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ((Int.castRingHom ℝ) (la τ i) - (Int.castRingHom ℝ) (la τ l))
      = ∏ i ∈ Finset.range N, ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)) N]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun l => if (i : ℕ) < l then v τ i - v τ l else 1) N, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext l; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]) fun l _ => ?_
    rw [hv, hv]
    rfl
  have rhs : ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l)
      = ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    have := Finset.mem_range.1 hl
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [lhs, rhs, Finset.prod_comm]

theorem rho_div_le : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv →
    (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H →
    24 * (N : ℝ) * W.T ≤ H →
    (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) →
    GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤
      3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  intro ι _ N W H hW hd hanti hw hH1 hH2 hbar
  have hk := hW.kc_pos
  have hkp := hW.kc_lt
  have hpN := hW.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast hW.weightConst_nonneg
  have hT1 : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast hW.h1
  have hD : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by linarith
  have hMT : M ≤ 5 / 4 * W.T := by linarith
  have hNT : 0 < (N : ℝ) * W.T := mul_pos hN0 hT0
  have hHpos : 0 < H := by linarith
  obtain ⟨g1, hg1⟩ : ∃ g1 : ℝ, g1 = H / (2 * M) := ⟨_, rfl⟩
  have hg : 3 * (N : ℝ) < g1 := by
    rw [hg1, lt_div_iff₀ (by positivity)]
    have : (N : ℝ) * M ≤ N * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hMT hN0.le
    nlinarith
  obtain ⟨U, hU⟩ : ∃ U : ι → ℕ → ℝ, ∀ τ (i : Fin N), U τ i = W.u1 τ i :=
    ⟨fun τ n => if h : n < N then (W.u1 τ ⟨n, h⟩ : ℝ) else 0, fun τ i => by simp [i.2]⟩
  have hU' : ∀ τ (i : Fin N), (if (i : ℕ) < W.p then U τ i else U τ i + 3 * N) = ((W.u' τ i : ℤ) : ℝ) := by
    intro τ i
    rw [hU]
    unfold Wts.u'
    split_ifs <;> push_cast <;> ring

  obtain ⟨a, ha⟩ : ∃ a : Fin N, (a : ℕ) = W.p - 1 := ⟨⟨W.p - 1, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N, (b : ℕ) = W.p := ⟨⟨W.p, hpN⟩, rfl⟩
  have hab : (b : ℕ) = a + 1 := by omega
  have hbarGap : ∀ τ, g1 ≤ (W.u1 τ a : ℝ) - W.u1 τ b := by
    intro τ
    have e := (hd τ).2 a b hab
    rw [if_pos hb] at e
    have hG := hbar τ a b hab hb
    have hMi : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    have h3 := Int.emod_lt_of_pos (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) hMi
    have h4 := Int.mul_ediv_add_emod (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) ((W.T : ℤ) + W.Dd + 1)
    rw [← e] at h4
    have h5 : W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2)) - ((W.T : ℤ) + W.Dd + 1) <
        ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) := by linarith
    have h6 : ((W.u τ a - W.u τ b : ℤ) : ℝ) - W.c0 - 2 * N + 2 - M < M * ((W.u1 τ a : ℝ) - W.u1 τ b) := by
      rw [hM]
      have := (Int.cast_lt (R := ℝ)).2 h5
      push_cast at this ⊢
      linarith
    rw [hg1, div_le_iff₀ (by positivity)]
    have h7 : H ≤ 2 * (M * ((W.u1 τ a : ℝ) - W.u1 τ b)) := by linarith
    linarith
  have hdec : ∀ τ i l, i < l → l < N → U τ l < U τ i := by
    intro τ i l h1 h2
    have := hU τ ⟨i, by omega⟩
    have := hU τ ⟨l, h2⟩
    simp only at *
    have h := hanti τ (show (⟨i, by omega⟩ : Fin N) < ⟨l, h2⟩ from h1)
    have h' : (W.u1 τ ⟨l, h2⟩ : ℝ) < W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast h
    linarith
  have hgap : ∀ τ i l, i < W.p → W.p ≤ l → l < N → g1 ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have m1 : W.u1 τ a ≤ W.u1 τ ⟨i, by omega⟩ := (hanti τ).antitone (show (⟨i, by omega⟩ : Fin N) ≤ a by
      rw [Fin.le_def]; simp only; omega)
    have m2 : W.u1 τ ⟨l, h3⟩ ≤ W.u1 τ b := (hanti τ).antitone (show b ≤ (⟨l, h3⟩ : Fin N) by
      rw [Fin.le_def]; simp only; omega)
    have m1' : (W.u1 τ a : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast m1
    have m2' : (W.u1 τ ⟨l, h3⟩ : ℝ) ≤ W.u1 τ b := by exact_mod_cast m2
    linarith [hbarGap τ]
  have hcl : ∀ τ i l, i < W.kc → W.p ≤ l → l < N → W.w τ / (2 * W.T) ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have c1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hd τ ⟨i, by omega⟩).2.2 h1
    have c1' : (0 : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast c1
    have c2 := ((GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hd τ).1 ⟨l, h3⟩ (by simp only; omega)).1
    linarith
  have L := GlobalTheory.degree_ratio_shift_bound ι N W.p W.kc U (fun _ => g1) W.w (W.T : ℝ) hkp.le hpN.le hT0 hw
    (fun _ => hg) hdec hgap hcl
  dsimp only at L
  obtain ⟨-, -, L3⟩ := L
  unfold GlobalTheory.CompHt.rhoOf
  rw [vdm_cast_eq_range W.u' (fun τ i => if i < W.p then U τ i else U τ i + 3 * N) (fun τ i => hU' τ i),
    vdm_cast_eq_range W.u1 U hU]
  refine L3.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity))
  have hwt := hw τ
  have e : ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) / g1 = ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) * (2 * M) / H := by
    rw [hg1]; field_simp
  rw [e]
  have i1 : ((W.p - W.kc : ℕ) : ℝ) ≤ N := by exact_mod_cast (show W.p - W.kc ≤ N by omega)
  have i2 : ((N - W.p : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - W.p ≤ N by omega)
  have i3 : (W.kc : ℝ) ≤ N := by exact_mod_cast (show W.kc ≤ N by omega)
  gcongr

end GlobalTheory.MeanTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeDefectLeOfDividedWeightStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.weightDegreeDefect_le_of_divided_weight : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv → (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H → 24 * (N : ℝ) * W.T ≤ H → (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) → GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤ 3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  first | exact @GlobalTheory.MeanTop.rho_div_le | exact GlobalTheory.MeanTop.rho_div_le | (intros; apply GlobalTheory.MeanTop.rho_div_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBounds

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct



noncomputable section

namespace GlobalTheory.CovTop.ZedSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem bar_gap (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (hi : (i : ℕ) + 1 < D.R.m) (τ : Psi p.T.Q.H)
    (a b : Fin ((dat p i).p + (dat p i).q)) (hab : (b : ℕ) = a + 1) (hb : (b : ℕ) = (dat p i).p) :
    LevelStarExponents.h0 L ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e1 := WtShape.dat_p p i
  have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) = WtShape.sgR D t a - WtShape.sgR D t (a + 1) - 1 +
      if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
    rw [Int.cast_sub, WtShape.uW_real p i τ t ht, WtShape.uW_real p i τ t ht, hab, ← WtShape.entR_step]; ring
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have h1 := WtShape.sgR_step_low D L P t a (by omega) (by omega)
  rw [if_pos (by omega)] at hd
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast WtShape.six_le_r D.R
  linarith

abbrev wp (p : PtAt ex Csz) (i : Fin D.R.m) (PP : ℝ) : WtPar (dat p i) :=
  ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩

theorem zed_at (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (T : ParamsT D L P) (A M C1 : ℝ)
    (hS : SizeAt p i T.PP C1) (hq : ∀ u1, Quo p i T.PP u1 → u1 = (wp p i T.PP).u₁)
    (hsa : ∀ τ, StrictAnti ((wp p i T.PP).u₁ τ)) (hH : HostNum D L T.PP A M) (hW : WtNum p i T.PP)
    (hi : (i : ℕ) + 1 < D.R.m) :
    zed p i T.PP (wp p i T.PP).u₁ * (T.PP * kap p i) ≤ L.sc.b / 2 := by
  obtain ⟨hb1, -, -, -, -, hbk, hquo⟩ := hS
  obtain ⟨u0, hu0⟩ := (hquo hi).1
  have hQ : Quo p i T.PP (wp p i T.PP).u₁ := hq u0 hu0 ▸ hu0
  obtain ⟨h0', S, eta, -, -, -, -, -, hHyp⟩ := hW.hyp hi
  have hDv : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).IsDiv := (quo_iff p i T.PP h0' S eta _).1 hQ
  have hY : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).Hyp := hHyp _
  have hDp : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := hW.dim.trans T.Dp_eq.symm
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hDp]; exact Nat.ceil_le.2 (WtShape.len_le D L P T)
  obtain ⟨s1, s2, -⟩ := WtShape.spacing_ge T ((i : ℕ) + 1) _ hlen
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hb0 : 0 < L.sc.b := by linarith
  have hsb : 0 < Real.sqrt L.sc.b := Real.sqrt_pos.2 hb0
  have hw : ∀ τ, Real.sqrt L.sc.b / 2 ≤ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) := fun τ => by
    have := hW.low τ; have := hH.low; linarith
  have hrho := GlobalTheory.T.weightDegreeDefect_le_of_divided_weight _ _ (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁) (LevelStarExponents.h0 L) hY hDv hsa
    (fun τ => lt_of_lt_of_le (by positivity) (hw τ))
    (by
      show 4 * (((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + (lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1) ≤ LevelStarExponents.h0 L
      rw [eN, hDp]; simpa [cZero] using s1)
    (by
      show 24 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) ≤ LevelStarExponents.h0 L
      rw [eN]; exact s2)
    (fun τ a b hab hb => bar_gap p i P hi τ a b hab hb)
  have hrB : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ = GlobalTheory.CompHt.rhoOf (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u'
      (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u1 := by
    unfold GlobalTheory.CompHt.rhoB; congr 1; funext τ j; rw [GlobalTheory.CompHt.uPrime_apply]; rfl
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hrho' : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ ≤ 3 * (D.R.r : ℝ) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) * (2 / Real.sqrt L.sc.b))) := by
    rw [hrB]
    refine hrho.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) *
      (2 / Real.sqrt L.sc.b)) fun τ _ => ?_) (by rw [eN]; positivity)).trans_eq ?_)
    · show (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (2 * ((lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1)) / LevelStarExponents.h0 L +
          2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) /
          (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ _
      rw [eN, hDp]
      have hwp : 0 < (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) :=
        lt_of_lt_of_le (by positivity) (hw τ)
      have h2 : 1 / (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 2 / Real.sqrt L.sc.b := by
        rw [div_le_div_iff₀ hwp hsb]; linarith [hw τ]
      have h3 : 0 ≤ 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      rw [mul_one_div] at h4
      linarith
    · rw [Finset.card_univ, nsmul_eq_mul, hcard, eN]
  have hk : kap p i ≤ 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
    show ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ _
    calc ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|
        ≤ ∑ τ : Psi p.T.Q.H, ∑ k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b := by
          gcongr with τ _ k _; exact hW.up τ k
      _ = 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hcard, eN]; ring
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have h8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
    linarith
  have hD1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast WtShape.one_le_Dp T
  have hTl : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ (lenT p i T.PP : ℝ) := by
    unfold lenT; rw [hDp]; exact Nat.le_ceil _
  have hTO : (lenT p i T.PP : ℝ) ≤ T.TO := by exact_mod_cast hlen
  have hT4 : 4 * (T.Dp : ℝ) + 4 ≤ lenT p i T.PP := by
    have := hY.h1
    have h : 4 * T.Dp + 4 ≤ lenT p i T.PP := by rw [← hDp]; exact this
    exact_mod_cast h
  have hH0 : (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP ≤ LevelStarExponents.h0 L := by
    refine le_trans ?_ T.heightBound_ge_order_product
    have hP : 0 ≤ T.PP := by linarith [WtShape.forty_le_PP T]
    have : 0 ≤ (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP := by positivity
    nlinarith [T.ChT_ge]
  have hn0 : 2500 * (D.R.r : ℝ) * ((T.Dp : ℝ) + 1) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have h' : 2500 * D.R.r * (T.Dp + 1) ≤ T.TO := le_trans (by
      rw [show 2500 * D.R.r * (T.Dp + 1) = 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) by ring]; exact Nat.le_add_left _ _) h
    exact_mod_cast h'
  have hnW : (D.R.f : ℝ) * D.R.r * ((D.R.r : ℝ) + 1) ≤ T.nWn := by exact_mod_cast T.nW_lo.1
  have hP3 : T.PP ^ 3 * (T.TO : ℝ) ^ 2 ≤ Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; exact T.precision_cube_order_sq_le_sqrt
  have hsp : (T.TO : ℝ) * T.nWn ≤ D.R.r + D.R.t := by
    have h := T.split
    have h' : T.TO * T.nWn ≤ D.R.r + D.R.t := by omega
    exact_mod_cast h'
  have hNb : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ D.R.N D.R.m := by
    have h' : D.R.m * (D.R.t + 1) ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast h'
  have key := GlobalTheory.T.seven_mul_height_bound_le_half_of_parameters (T.Dp : ℝ) (lenT p i T.PP : ℝ) (GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁) T.PP (kap p i) L.sc.b
    D.R.f D.R.r D.R.m D.R.k (LevelStarExponents.h0 L) T.TO (D.R.N D.R.m) T.nWn D.R.t hD1 hb0 hf1 hm2 hmk (WtShape.r_cast D.R)
    (Nat.cast_nonneg _) (sizeK_nonneg _ _ _) hk hTl hTO hT4 hrho' hH0 hn0 hnW T.PP_nW hP3 hsp hNb
  unfold zed
  rw [hDp]
  exact key

end GlobalTheory.CovTop.ZedSz
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZedSize

section

@[expose] public section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CovTop.ZedSz
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem zed_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 := by
  intro hS
  have hI := _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS
  have hHN := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  have hWN := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS hI) (Formalism.MainNotions.Closed.and hHN hWN)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩, ⟨C4, -, a4, h4⟩⟩ := hh
  refine ⟨0, le_rfl, max (max a1 a2) (max a3 a4), fun x hx hle ι p hp i hi Y _ => ?_⟩
  have e1 := h1 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle) ι p hp i
  have e2 := h2 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle) ι p hp i hi
  have e3 := h3 x hx (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle) ι p hp i
  have e4 := h4 x hx (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle) ι p hp i
  have key := zed_at p i (Fm.params x hx ι) (Fm.parT x hx ι) C3 1 C1 e1 e2.2.2.2.1 (fun τ => (e2.2.2.2.2.1 τ).1) e3 e4 hi
  have hb1 := e1.1
  have hbk := e1.2.2.2.2.2.1
  refine ⟨by linarith, ?_⟩
  by_contra hc
  push_neg at hc
  have : 1 / 2 * ((Fm.parT x hx ι).PP * kap p i) < _ * ((Fm.parT x hx ι).PP * kap p i) :=
    mul_lt_mul_of_pos_right hc (by linarith)
  linarith
end GlobalTheory.CovTop.ZedSz
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZedSizeStatement

section

@[expose] public section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weight_parameter_size_bounds' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 := by
  first | exact @_root_.GlobalTheory.CovTop.ZedSz.zed_size_alt | exact _root_.GlobalTheory.CovTop.ZedSz.zed_size_alt | (intros; apply _root_.GlobalTheory.CovTop.ZedSz.zed_size_alt <;> assumption)
end
end
end
