module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.DetInvNe
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.JacobiBlocks
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexedStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPushStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SameOrbitTrans

-- Source module: Development.WeilBound.CoreStatements.JacobiBlockDeterminants.ValDetFac

section

@[expose] public section

noncomputable section

namespace HeightCancellation.C2

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB SquareStatements.Sing
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)

variable {p q : ℕ}

theorem col_val (a : Fin (p + q)) : (SquareStatements.Sing.col p q a : ℕ) = if (a : ℕ) < p then q + a else a - p := by
  unfold SquareStatements.Sing.col
  split_ifs <;> rfl

theorem prod_col {R : Type} [CommRing R] (f : Fin (p + q) → R) (i : Fin (p + q)) :
    ∏ a ∈ Finset.Iic i, f (SquareStatements.Sing.col p q a) = (∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => q ≤ c ∧ (c : ℕ) ≤ q + i, f c) *
      ∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i, f c := by
  rw [← Finset.prod_union (Finset.disjoint_filter.2 fun c _ h h' => by omega)]
  refine Finset.prod_bij (fun a _ => SquareStatements.Sing.col p q a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    have h1 : (a : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 ha)
    have h2 := a.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, col_val]
    split_ifs <;> omega
  · intro a _ b _ h
    have h1 := congrArg Fin.val h
    have h2 := a.2
    have h3 := b.2
    rw [col_val, col_val] at h1
    refine Fin.ext ?_
    split_ifs at h1 <;> omega
  · intro c hc
    have h2 := c.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with hc | hc
    · refine ⟨⟨c - q, by omega⟩, Finset.mem_Iic.2 (show c - q ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_pos (show c - q < p by omega)]
      show q + (c - q) = c
      omega
    · refine ⟨⟨c + p, by omega⟩, Finset.mem_Iic.2 (show c + p ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_neg (show ¬ c + p < p by omega)]
      show c + p - p = c
      omega

open Classical in
theorem prod_diag {R : Type} [CommRing R] {B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hB : B.BlockTriangular id)
    (i : Fin (p + q)) : ∏ a ∈ Finset.Iic i, B (SquareStatements.Sing.col p q a) (SquareStatements.Sing.col p q a) =
      detFac p i B * if IsProperStep (p + q) p i then ∏ c ∈ stepCols (p + q) p i, B c c else 1 := by
  have hi := i.2
  rw [prod_col (fun c => B c c), detFac, MinorCalc.minorIJ_self_of_triangular B hB,
    MinorCalc.minorIJ_self_of_triangular B hB]
  unfold IsProperStep stepCols wIdx omIdx
  have key : ∀ {P Q : Fin (p + q) → Prop} [DecidablePred P] [DecidablePred Q], (∀ c, P c ↔ Q c) →
      ∏ c ∈ Finset.univ.filter P, B c c = ∏ c ∈ Finset.univ.filter Q, B c c := fun h => by
    rw [Finset.filter_congr fun c _ => h c]
  have key0 : ∀ {P : Fin (p + q) → Prop} [DecidablePred P], (∀ c, ¬ P c) →
      ∏ c ∈ Finset.univ.filter P, B c c = 1 := fun h => by
    rw [Finset.filter_eq_empty_iff.2 fun c _ => h c, Finset.prod_empty]
  by_cases hN : (i : ℕ) + 1 = p + q
  · rw [if_pos (by omega), if_pos hN, if_neg (fun h => h.2 hN), mul_one]
    congr 1
    · exact key fun c => by have := c.2; omega
    · exact key fun c => by have := c.2; omega
  · rw [if_neg hN, mul_one]
    rcases lt_trichotomy ((i : ℕ) + 1) p with h | h | h
    · rw [if_neg (by omega), if_pos ⟨h.ne, hN⟩, one_mul, key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega), mul_one]
      exact key fun c => by rw [if_pos h.le]; omega
    · rw [if_pos h.ge, if_neg (fun h' => h'.1 h), key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega)]
      congr 1
      exact key fun c => by have := c.2; omega
    · rw [if_pos h.le, if_pos ⟨h.ne', hN⟩]
      congr 1
      · exact key fun c => by have := c.2; omega
      · exact key fun c => by rw [if_neg (by omega)]; omega

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {N : ℕ}

theorem val_detFac (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) (j : ℕ) (i : Fin N) : ValAt ξ z (detFac j i A) (detFac j i h) := by
  choose _ s hs hs' using hv
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  exact ⟨hz, detFac j i (Matrix.of s), by rw [e1, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map],
    e2 ▸ (PositivityTheory.Xgp.c_bm_exists_hom.detFac_map (Scheme.stalkClosedPointTo z).hom i (Matrix.of s)).symm⟩

theorem val_pl (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) {u : Finset (Fin N) → Ω} {v : Finset (Fin N) → ℂ}
    (hu : ∀ I, ValAt ξ z (u I) (v I)) (C : Finset (Fin N)) :
    ValAt ξ z (∑ I, u I * minorIJ A I C) (∑ I, v I * minorIJ h I C) := by
  choose _ s hs hs' using hv
  choose _ t ht ht' using hu
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  refine ⟨hz, ∑ I, t I * minorIJ (Matrix.of s) I C, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
      exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map, ht]
  · rw [e2]
    refine (map_sum (Scheme.stalkClosedPointTo z).hom _ _).trans (Finset.sum_congr rfl fun I _ => ?_)
    exact (map_mul (Scheme.stalkClosedPointTo z).hom _ _).trans (congrArg₂ (· * ·) (ht' I)
      (CPts.minorIJ_map (Scheme.stalkClosedPointTo z).hom (Matrix.of s) I C).symm)

end Val

end HeightCancellation.C2

open AlgebraicGeometry Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB HeightCancellation.C2 SquareStatements.Sing in
theorem HeightCancellation.c2 : SquareStatements.Sing.C2 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐' z wb F τ B h hF gd hval hx ⟨bB, tB, _, _, _, hv⟩ i
  classical
  have hz := 𝔐'.all (centre z)
  have hT : ((F.T τ).map (algebraMap M.Ω Φ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (hF.1 τ).2
  have bT : IsBlockDiag D.p ((F.T τ).map (algebraMap M.Ω Φ)) := (hF.1 τ).1.map _
  have bX : IsBlockDiag D.p (inFrame M F τ B) := ((bT.inv hT.isUnit).mul (M.g_block τ)).mul bB
  have e : (F.T τ).map (algebraMap M.Ω Φ) * inFrame M F τ B = M.g τ * B := by
    rw [inFrame, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hT.isUnit]
  have e1 : algebraMap M.Ω Φ (detFac D.p i (F.T τ)) * detFac D.p i (inFrame M F τ B) =
      detFac D.p i (M.g τ) * detFac D.p i B := by
    rw [← MinorCalc.detFac_mul i bB, ← e, MinorCalc.detFac_mul i bX, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map]
  have e2 : algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') *
      ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k') = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow₀, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ ((map_ne_zero _).2 (hx k)))]
  have vd := val_detFac hz hv D.p i
  refine ⟨fun k hk m => ?_, fun hk => ?_⟩
  · have hp : IsProperStep (D.p + D.q) D.p i := by
      by_contra hn
      rw [(M.blk_none (τ, i)).2 hn] at hk
      cases hk
    have e3 := CPts.frame_gen M hF (RingHom.id Φ) (p := (τ, i)) hk m bX bB tB e
    simp only [RingHom.id_apply] at e3
    have v2 := val_pl hz hv (fun I => hval _ (gd.2.1 ⟨k, m⟩ I).1) (stepCols (D.p + D.q) D.p i)
    convert CxVal.mul vd v2 using 1
    rw [prod_diag tB, if_pos hp]
    linear_combination (-(∏ c ∈ stepCols (D.p + D.q) D.p i, B c c) * y ⟨k, m⟩ *
        ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
      (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
      (detFac D.p i (inFrame M F τ B) * ∑ I, algebraMap M.Ω Φ (F.u ⟨k, m⟩ I) *
        minorIJ (inFrame M F τ B) I (stepCols (D.p + D.q) D.p i)) * e2
  · have hp : ¬ IsProperStep (D.p + D.q) D.p i := (M.blk_none (τ, i)).1 hk
    obtain ⟨h0, r1, r2⟩ := gd.2.2 (τ, i) hk
    have v1 := hval _ r1
    have v2 := hval _ r2
    refine ⟨fun hv0 => ?_, ?_⟩
    · have v3 := CxVal.mul v1 v2
      rw [← map_mul, mul_inv_cancel₀ h0, map_one, hv0, zero_mul] at v3
      exact zero_ne_one (CxVal.unique v3 (CxVal.one hz))
    · have e3 := congrArg (algebraMap M.Ω Φ) (hF.2.2.2 (τ, i) hk)
      rw [map_mul, map_mul] at e3
      convert CxVal.mul vd v1 using 1
      rw [prod_diag tB, if_neg hp]
      linear_combination (-algebraMap M.Ω Φ (M.lam (τ, i)) *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
        (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
        (detFac D.p i (inFrame M F τ B) * algebraMap M.Ω Φ (F.υ (τ, i))) * e2
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.BlockDiagMinorNeZero

section

@[expose] public section

noncomputable section

namespace SquareStatements.Sing

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB
  GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}

theorem mem_regRing_of_regAt (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal w) s) :
    s ∈ regRing x w := by
  exact ValRing.exists_isValueAt hw hs

theorem valAt_one_multihomogeneous_squares (hw : w ∈ mcPts (mCoordIdeal x)) : valAt x (1 : Ω) w = 1 := (regVal hw).map_one

theorem valAt_zero_multihomogeneous_squares (hw : w ∈ mcPts (mCoordIdeal x)) : valAt x (0 : Ω) w = 0 := (regVal hw).map_zero

theorem valAt_sum_mul' (hw : w ∈ mcPts (mCoordIdeal x)) {σ : Type} (S : Finset σ) (a b : σ → Ω)
    (ha : ∀ m, a m ∈ regRing x w) (hb : ∀ m, b m ∈ regRing x w) :
    valAt x (∑ m ∈ S, a m * b m) w = ∑ m ∈ S, valAt x (a m) w * valAt x (b m) w := by
  have e : (∑ m ∈ S, a m * b m) =
      ((∑ m ∈ S, (⟨a m, ha m⟩ : regRing x w) * ⟨b m, hb m⟩ : regRing x w) : Ω) := by
    push_cast; rfl

  rw [e, ← regVal_apply hw, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, regVal_apply, regVal_apply]

end Val

theorem block_diag_minor_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hb : IsBlockDiag j h)
    (hd : h.det ≠ 0) : ∃ I, IsStepRows N j i I ∧ minorIJ h I (stepCols N j i) ≠ 0 := by
  classical
  set J := stepCols N j i with hJ
  set k := J.card with hk
  let e := J.orderEmbOfFin (rfl : J.card = k)
  let A : Matrix (Fin N) (Fin k) ℂ := fun r c => h r (e c)
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hcol : LinearIndependent ℂ A.col :=
    (Matrix.linearIndependent_cols_iff_isUnit.2 hu).comp e e.injective
  have hrank : A.rank = k := by
    rw [← Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hcol, Fintype.card_fin]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ A.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let I : Finset (Fin N) := Finset.univ.image a
  have hI : I.card = k := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, hcard]
  have hmemI : ∀ t : Fin k, ∃ c : κ, a c = I.orderEmbOfFin hI t := by
    intro t
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem I hI t)
    exact ⟨c, hc⟩
  choose f hf using hmemI
  have hfinj : Function.Injective f := by
    intro s t hst
    have : I.orderEmbOfFin hI s = I.orderEmbOfFin hI t := by rw [← hf s, ← hf t, hst]
    exact (I.orderEmbOfFin hI).injective this
  have hrows : LinearIndependent ℂ (h.submatrix (I.orderEmbOfFin hI) e).row := by
    have h2 := hli.comp f hfinj
    have heq : (h.submatrix (I.orderEmbOfFin hI) e).row = (A.row ∘ a) ∘ f := by
      funext t c
      simp [Matrix.row, A, hf]
    rw [heq]
    exact h2
  refine ⟨I, ⟨hI, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    have hne : A.row (a c) ≠ 0 := by
      have := hli.ne_zero c
      simpa using this
    by_contra hnot
    apply hne
    funext t
    simp only [Matrix.row, A, Pi.zero_apply]
    apply hb
    have hc := MinorCalc.mem_stepCols_block (i := i) (c := e t) hj (Finset.orderEmbOfFin_mem J _ t)
    split_ifs at hc hnot with hij
    · simp [wIdx] at hnot
      intro hiff
      have h3 : (a c : ℕ) < N - j := by omega
      exact absurd (hiff.1 h3) (by omega)
    · simp [omIdx] at hnot
      intro hiff
      exact absurd (hiff.2 hc) (by omega)
  · rw [MinorCalc.minorIJ_eq_det h I J k hI rfl]
    have := Matrix.linearIndependent_rows_iff_isUnit.1 hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

theorem c5 : C5 := by
  intro K _ ι _ Φ _ y Ψ N j M wb F h p k hw hF hG hb hd hk
  classical
  obtain ⟨I0, hI0, hne⟩ := block_diag_minor_ne_zero M.j_le p.2 h hb hd
  set J := stepCols N j p.2 with hJ
  by_contra hall
  push_neg at hall
  have hreg : ∀ (q : (k : K) × ι k) (I : Finset (Fin N)),
      F.u q I ∈ regRing M.x wb ∧ F.u' I q ∈ regRing M.x wb :=
    fun q I => ⟨mem_regRing_of_regAt hw (hG.2.1 q I).1, mem_regRing_of_regAt hw (hG.2.1 q I).2⟩
  have key : ∀ I : Finset (Fin N), IsStepRows N j p.2 I →
      ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb * valAt M.x (F.u ⟨k, m⟩ I) wb =
        if I0 = I then 1 else 0 := by
    intro I hI
    rw [← valAt_sum_mul' hw Finset.univ (fun m => F.u' I0 ⟨k, m⟩) (fun m => F.u ⟨k, m⟩ I)
      (fun m => (hreg _ _).2) (fun m => (hreg _ _).1)]
    rw [hF.2.2.1 p k hk I0 I hI0 hI]
    split_ifs
    · exact valAt_one_multihomogeneous_squares hw
    · exact valAt_zero_multihomogeneous_squares hw
  have hterm : ∀ I : Finset (Fin N),
      ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb * (valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I J) =
        if I0 = I then minorIJ h I J else 0 := by
    intro I
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    by_cases hI : IsStepRows N j p.2 I
    · rw [key I hI]
      split_ifs <;> simp
    · rw [MinorCalc.minor_stepCols_eq_zero M.j_le h I hb hI]
      split_ifs with e
      · subst e
        exact absurd hI0 hI
      · simp
  have hsum : ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb *
      ∑ I : Finset (Fin N), valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I J = minorIJ h I0 J := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hterm]
    simp
  apply hne
  rw [← hsum]
  simp [hall]

end SquareStatements.Sing
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsValueAtValAtOfRegAt

section

@[expose] public section

noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt IsValueAt)

theorem isValueAt_valAt_of_regAt {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    {x : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : IsValueAt x s w (valAt x s w) := by
  obtain ⟨d, g, h, hg, hh, hQ, hgh⟩ := hs
  have hwh : (MvPolynomial.eval w) ((MvPolynomial.map (Int.castRingHom ℂ)) h) ≠ 0 := by
    intro h0
    apply hQ
    apply GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hh
    rw [MvPolynomial.eval_map] at h0
    simpa [MvPolynomial.aeval_def] using h0
  have hxh : (MvPolynomial.aeval x) h ≠ 0 := by
    intro h0
    exact hwh (hw.2 h (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have hex : ∃ v, IsValueAt x s w v := ⟨_, d, g, h, hg, hh, hxh, hgh, hwh, rfl⟩
  unfold GroundTheory.Heights₂.Heights.LowerBoundFree.valAt
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem c0 : C0 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 𝔐' pr j z w hO hw
  obtain ⟨hd, hf, -, -, -⟩ := hO
  obtain ⟨-, -, hval⟩ := GlobalTheory.T.dominating_regular_push 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) hd 𝔐'.tie.gen
  have hval' : ∀ (a : M.Ω) (r : ℂ), ValAt 𝔐.ξ (z ≫ pr) a r → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ a) r :=
    fun a r => hval z a r (𝔐'.all _)
  have hco : CoordsAt 𝔐.ξ M.x (z ≫ pr) (basePart M.blk w) :=
    GlobalTheory.T.dominating_coords_reindexed 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) (NonPluckerBlocks M.blk) K (baseIdx ι M.blk) ι M.x y
      Subtype.val (fun _ => Equiv.refl _) hd 𝔐.tie 𝔐'.all (fun k a => M.y_base ⟨k, a⟩)
      (fun z' a r h' => hval z' a r (𝔐'.all _) h') z w hw
  refine ⟨hco, GlobalTheory.CompanionTheory.Ar.Chg.mem_abLocus_iff 𝔐 𝔐' pr hf (centre z), hval', fun s hs => hval' _ _ ?_⟩
  have hm : basePart M.blk w ∈ mcPts (mCoordIdeal M.x) :=
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).2 ⟨z ≫ pr, 𝔐.all _, hco⟩
  exact (GlobalTheory.T.valAt_iff_value_at 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie (z ≫ pr) _ (𝔐.all _) hco s _).2
    (isValueAt_valAt_of_regAt hm hs)

end SquareStatements.Sing
end
end
end

-- Source module: Development.WeilBound.CoreStatements.JacobiBlockDeterminants.StSing

section

@[expose] public section

theorem HeightCancellation.stSing : SquareStatements.StSing :=
  SquareStatements.Sing.stSing_of SquareStatements.Sing.c0 HeightCancellation.G.c1 HeightCancellation.c2 SquareStatements.Sing.c5 HeightCancellation.G.c3w HeightCancellation.G.c3o HeightCancellation.c4
end
end
