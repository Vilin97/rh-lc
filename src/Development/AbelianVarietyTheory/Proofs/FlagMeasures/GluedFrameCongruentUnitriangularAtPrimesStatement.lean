module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruence
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameScaleIsUnitAtPrimeOverLevelStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitAndSmulCompletedLatticeLeAtLevelPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangularStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLattice

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowFrame

theorem one_mem_ddS_zpow (D : D7) (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hI0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    rw [Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hI1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hJ0 : ddS D ^ n ≠ 0 := pow_ne_zero _ hI0
  have hJ1 : ddS D ^ n ≤ 1 := pow_le_one' hI1 n
  rw [zpow_neg, zpow_natCast]
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹ := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = ddS D ^ n * (ddS D ^ n)⁻¹ :=
          (mul_inv_cancel₀ hJ0).symm
      _ ≤ 1 * (ddS D ^ n)⁻¹ := by gcongr
      _ = (ddS D ^ n)⁻¹ := one_mul _
  exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)

theorem frame_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) :
    IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  rintro ⟨-, ⟨-, -, hlift, -⟩, hX⟩ a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact hlift.1
  · have e : frame (lf D F0) i.castSucc = F0.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : F0.e i ∈ XS D F0 := by
      apply Submodule.subset_span
      refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
        rw [Nat.cast_sub i.isLt.le]
      rw [hk]
      exact one_mem_ddS_zpow D _
    rw [← hX] at hmem
    exact hmem.1

end GlobalTheory.Unfold.RowFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLatticeStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice : ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  first | exact @GlobalTheory.Unfold.RowFrame.frame_mem | exact GlobalTheory.Unfold.RowFrame.frame_mem | (intros; apply GlobalTheory.Unfold.RowFrame.frame_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAdaptedIsometryFrameUpperTriangularExpansio

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Sloc.AdaptExpand

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem exists_coeff {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ l : Fin D.R.rS → D.host.E, (∀ i, b.val ≤ i.val → l i = 0) ∧ x = ∑ i, l i • F.fl.e i := by
  have hx' : x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < b.val}) := hx
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx'
  obtain ⟨l, hl, rfl⟩ := hx'
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    have := hl (Finsupp.mem_support_iff.2 h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem exists_coeff_frame {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ u : Fin (D.R.rS + 1) → D.host.E, (∀ c, b ≤ c → u c = 0) ∧ x = ∑ c, u c • frame F c := by
  obtain ⟨l, hl, rfl⟩ := exists_coeff F b x hx
  refine ⟨Fin.snoc (α := fun _ => D.host.E) l 0, fun c hc => ?_, ?_⟩
  · induction c using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hl i (by simpa [Fin.le_def] using hc)
  · rw [Fin.sum_univ_castSucc]
    simp [frame_castSucc]

theorem adapt_expand : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  intro D T F0 F g hg Z p Af hAf
  subst hAf
  have hu := fun c => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p c
  choose u hu0 hux using fun b => exists_coeff_frame F b _ (hg.2 b)
  refine ⟨fun a b => ((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a),
    fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp [hu0 b a hab.le, (ne_of_lt hab).symm]
  · simp [hu0 a a le_rfl]
  · have e1 : g (frame F0 b) = frame F b + ∑ c, u b c • frame F c := by
      rw [← hux b]; abel

    rw [e1, map_add (f := _), map_sum]
    simp only [baseChange_smul₂]
    have e2 : ∀ a, (((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a)) •
        (frFac Z.δ p a • baseChange₂ D p (frame F a)) =
        (D.s.atP p).ιE (u b a) • baseChange₂ D p (frame F a) + if a = b then baseChange₂ D p (frame F a) else 0 := by
      intro a
      rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel _ (hu a), mul_one, add_smul]
      split_ifs <;> simp
    simp only [e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel

end GlobalTheory.Sloc.AdaptExpand
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAdaptedIsometryFrameUpperTriangularExpansioStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  first | exact @GlobalTheory.Sloc.AdaptExpand.adapt_expand | exact GlobalTheory.Sloc.AdaptExpand.adapt_expand | (intros; apply GlobalTheory.Sloc.AdaptExpand.adapt_expand <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimes

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GluedCong

theorem bc_eq (D : D7) (Z : LocDat D) (p : PlF D) (v : (VS D).V) :
    (GlobalTheory.HL.placesOf Z).bc p ((VS D).frame.equivFun v) = baseChange₂ D p v := by
  funext i; rfl

theorem lat_eq (D : D7) (Z : LocDat D) (p : PlF D) (L : LV D) :
    (GlobalTheory.HL.placesOf Z).lat p (L.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))) = lattice₂ D Z.M p L := by
  unfold GlobalTheory.HL.Places.lat lattice₂
  congr 1
  ext z
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (bc_eq D Z p v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, bc_eq D Z p v⟩

theorem smul_mem_gmap (D : D7) (γ : GV D) (I : Ideal (𝓞 D.host.E))
    (L : LV D) (v : (VS D).V) (s : 𝓞 D.host.E) (h : s • v ∈ I • L) :
    s • γ v ∈ I • Formalism.HermitianLatticesTheory.gmap γ L := by
  have hg1 : I • Formalism.HermitianLatticesTheory.gmap γ L = (I • L).map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_smul'']
  rw [hg1]
  refine Submodule.mem_map.2 ⟨s • v, h, ?_⟩
  exact (γ : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower s v



theorem glued_loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP
  obtain ⟨sg, hsp, hdict⟩ := GlobalTheory.T.split_and_smul_completedLattice_le_at_level_prime D Z P hP
  have hL0 := hL
  obtain ⟨hlat, hloc⟩ := hL
  obtain ⟨τ, hτ, hτL⟩ := hloc (below D P)
  obtain ⟨B, hB1, hB2, hBy⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u)) F g hA Z (below D P) (FP (below D P)).A.f (hB (below D P)).1
  obtain ⟨B', hB1', hB2', hBx⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u')) F' g' hA' Z (below D P) (FP (below D P)).B.f (hB (below D P)).2.1
  have hU := GlobalTheory.T.frameScale_isUnit_at_prime_over_level D (Tu D u) (Tu D u') (X.Fu u) F F' Z FP hB Λ y hL0 g hA hr P hP
  have hmemg : ∀ (γ : GV D) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T), IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) →
      ∀ a, γ (frame (lf D F0) a) ∈ Λ := by
    intro γ T F0 h a
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.1 (GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice D F0 _ h a)
    have e : γ (frame (lf D F0) a) = v := by
      rw [← hve]
      show γ (γ⁻¹ v) = v
      exact γ.apply_symm_apply v
    rw [e]; exact hv
  have hyL : ∀ a, baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g (X.Fu u) hr a, rfl⟩
  have hxL : ∀ a, baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g' (X.Fu u') hr' a, rfl⟩
  obtain ⟨ξp, hξO, hξ1, hξ2, hξc⟩ := GlobalTheory.T.term_families_congr_mod_unitriangular (locH Z (below D P)) (FP (below D P)) (y (below D P)) τ sg hsp hτ
    (fun b => baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) b))) (fun b => baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) b))) B B' hB1 hB1'
    (fun a => by rw [hB2, hB2'])
    (fun a => by
      rw [hB2]
      exact ⟨(hU a).2, frFac Z.δ (below D P) a, (hU a).1, Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z (below D P) a)⟩)
    hBy hBx hyL hxL
  have hfg : (Λ.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))).FG := hlat.fg.map _
  have hpos : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.HL.LocCongApprox.loc_cong_approx (GlobalTheory.HL.placesOf Z) (nV D) D.R.rS _ hfg
    (gS D) hpos (below D P) (fun a => (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)))
    (fun b => (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b))) ξp hξO hξ1 hξ2
    (fun a => by
      rw [lat_eq, bc_eq, ← hτL]
      exact hyL a)
    (fun b => by
      rw [← Submodule.map_smul'', lat_eq]
      have h1 := hdict Λ _ (hτL ▸ hξc b)
      simp only [bc_eq]
      exact h1)
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  obtain ⟨v, hv⟩ : ∃ v, v = g' (frame (lf D (X.Fu u')) b) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • g (frame (lf D (X.Fu u)) a) := ⟨_, rfl⟩
  have hφv : (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b)) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)) = (VS D).frame.equivFun v := by

    rw [hv, map_sub, map_sum]
    simp only [map_smul]
  rw [hφv] at h
  obtain ⟨s, hs, hsv⟩ := h
  rw [← Submodule.map_smul''] at hsv
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hzs : z = s • v := by
    apply ((VS D).frame.equivFun).injective
    have e1 : (VS D).frame.equivFun z = s • (VS D).frame.equivFun v := hzv
    rw [e1]
    exact (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).map_smul_of_tower s v).symm
  have hiso : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hA.1) hA'.1
  have hfr : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b = (g⁻¹ * g') (frame (lf D (X.Fu u')) b) := by
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(g⁻¹ * g')) _ _) b).symm
  have htarget : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b = g⁻¹ v := by

    rw [hfr, hv, map_sub, map_sum, LinearEquiv.mul_apply]
    unfold frameAct
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun a _ => ?_)
    exact (((g⁻¹ : GV D).map_smul _ _).trans (congrArg _ (g.symm_apply_apply _))).symm
  have hsv' : s • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    rw [← hzs]; exact hz
  refine ⟨s, hs, ?_⟩
  rw [htarget]
  exact smul_mem_gmap D g⁻¹ (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}) Λ v s hsv'

end GlobalTheory.Unfold.GluedCong
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimesStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  first | exact @GlobalTheory.Unfold.GluedCong.glued_loc_cong | exact GlobalTheory.Unfold.GluedCong.glued_loc_cong | (intros; apply GlobalTheory.Unfold.GluedCong.glued_loc_cong <;> assumption)
end
end
