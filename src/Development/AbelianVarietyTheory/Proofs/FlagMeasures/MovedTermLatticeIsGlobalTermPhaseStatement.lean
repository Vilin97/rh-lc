module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInvStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsLocalTermAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiOfEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimpleRootCoefEqSuperdiagonalSumFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularFrameChangeFromLinearAutStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularMulInvSuperdiagonalSumSubStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulTheta

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulThetaStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  first | exact @GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | exact GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | (intros; apply GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLattice

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem isLattice_map_equiv {E : Type} [Field E] [NumberField E] {V W : Type} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (e : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)

theorem term_lat_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  intro D X Y u u' Z T T' F0 F0' FP G c t ρ
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hL : Submodule.IsLattice D.host.E t.lam := hrow.1.1.toIsLattice
  exact isLattice_map_equiv (ρ.trans c.e) t.lam hL

end GlobalTheory.HL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLatticeStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedRowLattice_term_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  first | exact @GlobalTheory.HL.term_lat_isLattice | exact GlobalTheory.HL.term_lat_isLattice | (intros; apply GlobalTheory.HL.term_lat_isLattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhase

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermPhase

theorem exists_termFrame_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u'), ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ := by
  intro D X Y u u' t
  exact t.rep.2.2.2.2.2.1

theorem psiInf_exp : ∀ {E : Type} [Field E] [NumberField E] (g : ℕ) (x y : E), Complex.exp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (x / g) : ℚ) : ℂ))) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ ∧ Formalism.L2.SG.PairVal.psiInf g (x - y) = Formalism.L2.SG.PairVal.psiInf g x * (Formalism.L2.SG.PairVal.psiInf g y)⁻¹ := by
  intro E _ _ g x y
  refine ⟨?_, ?_⟩
  · have hx : x / (g : E) = ((g : ℚ)⁻¹) • x := by
      rw [Algebra.smul_def, div_eq_inv_mul]
      simp
    rw [Formalism.L2.SG.PairVal.psiInf, ← Complex.exp_neg, hx, LinearMap.map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  · simp only [Formalism.L2.SG.PairVal.psiInf, map_sub]
    rw [← div_eq_mul_inv, ← Complex.exp_sub]
    congr 1
    push_cast
    ring

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hg0, hcg⟩ := GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hlat := GlobalTheory.T.movedRowLattice_term_isLattice D X Y u u' _ F00 F'0 FP G c t₀ ρ
  have hU := hMv.2.1
  have hU' := hMv.2.2.1

  have hext : ∀ (N : G.GLV) p, ∃ m : (G.S p).GLV, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m :=
    fun N p => ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 N).exists

  have key : ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ →
      ∃ N N' : G.GLV, (∀ b, N (G.f b) = ∑ a, U a b • G.f a) ∧
        (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) ∧
        ∀ p (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m →
          (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' →
          (G.S p).IsTerm ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) ∧
            (G.S p).om ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) =
              (G.S p).psi m * ((G.S p).psi' m')⁻¹ := by
    intro ξ hξ
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    obtain ⟨hBl, hBd, -⟩ := GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd
    obtain ⟨⟨N, hN⟩, -⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U
      (fun i j h => (hU i j).1 h) (fun i => (hU i i).2 rfl)
    obtain ⟨-, ⟨N', hN'⟩⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G
      (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) hBl hBd
    refine ⟨N, N', hN, hN', ?_⟩
    intro p m m' hm hm'
    obtain ⟨t, d, hto, hlatEq, hf, hf'⟩ := GlobalTheory.T.movedTerm_lattice_isLocalTerm_at_place D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U'
      hMv p ξ hξ N N' hN hN' m m' hm hm'
    obtain ⟨h1, -⟩ := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
      D.R.rS D.R.k (FP p) (G.S p) (c.c p)
    obtain ⟨hT, hom, -⟩ := h1 d t hto
    rw [hlatEq] at hT hom
    have : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
    have : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
    have hd := (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L p) D.R.rS D.R.k (G.S p)).1 _ _ hT
    rw [hd] at hT hom
    have hpsi := GlobalTheory.T.localTermWeight_eq_character_mul_inv (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
      (c.c p) d t hto m m' hf hf'
    exact ⟨hT, hom ▸ hpsi⟩

  have hsig : ∀ x, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]
    exact (Formalism.BasicNotions.bridge_star_holds _ D.host x).symm
  have hprod := fun (n : G.GLV) (m : ∀ p, (G.S p).GLV)
      (hx : ∀ p, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p n (m p)) =>
    GlobalTheory.HL.PhaseProduct.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G D.sp.cm hsig
      (fun p => Units.mk0 (Y.δ p) (Y.agree p).2.1) (gS D) hg0
      (fun p y => (Y.agree p).2.2.2.2.1 y)
      (fun p => hcg p) n m hx
  obtain ⟨ξ₀, hξ₀⟩ := exists_termFrame_admissibilityWitness D X Y u u' t₀
  refine ⟨⟨hlat, fun p => ?_⟩, ?_⟩
  · obtain ⟨N, N', -, -, hloc⟩ := key ξ₀ hξ₀
    obtain ⟨m, hm⟩ := hext N p
    obtain ⟨m', hm'⟩ := hext N' p
    exact (hloc p m m' hm hm').1
  · intro ξ hξ
    obtain ⟨N, N', hN, hN', hloc⟩ := key ξ hξ
    choose m hm using hext N
    choose m' hm' using hext N'
    obtain ⟨hP, -, hfin⟩ := hprod N m hm
    obtain ⟨-, hP', hfin'⟩ := hprod N' m' hm'
    have hom : G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) =
        ∏ᶠ p, ((G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹) :=
      finprod_congr fun p => (hloc p (m p) (m' p) (hm p) (hm' p)).2
    have hs1 : (Function.mulSupport fun p => (G.S p).psi (m p)).Finite :=
      hfin.subset fun p hp => Or.inl hp
    have hs2 : (Function.mulSupport fun p => ((G.S p).psi' (m' p))⁻¹).Finite :=
      hfin'.subset fun p hp => Or.inr fun h => (Function.mem_mulSupport.1 hp) (by simp [h])
    rw [hom, finprod_mul_distrib hs1 hs2, finprod_inv_distrib, hP, hP',
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U N).1 hN,
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G _ N').2 hN',
      (psiInf_exp (gS D) _ 0).1, (psiInf_exp (gS D) _ 0).1, inv_inv]
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    rw [(GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd).2.2,
      (psiInf_exp (gS D) _ _).2, mul_assoc]

end GlobalTheory.HL.MovedTermPhase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedTermLattice_isGlobalTerm_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  first | exact @GlobalTheory.HL.MovedTermPhase.main | exact GlobalTheory.HL.MovedTermPhase.main | (intros; apply GlobalTheory.HL.MovedTermPhase.main <;> assumption)
end
end
