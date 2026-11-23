module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrameStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowRepresentativesUpToFrameAdaptedIsometryStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedTermFrameAdmissibleIntegral

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.AdmGlued

theorem gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem mem_localization_of_mem' {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L : LV D} {x : (VS D).V}
    (hx : x ∈ L) : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) :=
  ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L M : LV D} (h : L ≤ M) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem frame_mem_locP {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) (h : IsRowLat D F0 Λ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  obtain ⟨-, ⟨-, -, hlift, hconv⟩, -⟩ := h
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : (lf D F0).fl.z ∈ Λ := hlift.1
    have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact mem_localization_of_mem' P hz
  · obtain ⟨c, -, hc1, heq⟩ := hconv.1 P
    have e : frame (lf D F0) i.castSucc = (lf D F0).fl.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : (lf D F0).fl.e i ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F0).fl.e a) := by
      have := Submodule.subset_span (R := 𝓞 D.host.E) ⟨i, rfl⟩ (s := Set.range fun a => c a • (lf D F0).fl.e a)
      simpa [hc1 hP i] using this
    have h1 := mem_localization_of_mem' P hmem
    rw [← heq] at h1
    exact localization_mono P inf_le_left h1

theorem glued_frame_PD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D (X.Fu u)) u' (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr'
  have hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA.1
  have hg' : g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA'.1
  have hβ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg) hg'
  have hmap : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) = Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hmapL : mapLF (g⁻¹ * g') (lf D (X.Fu u')) = Formalism.L2.SG.Saturated.mapL (g⁻¹ * g') hβ (lf D (X.Fu u')) := by
    unfold mapLF; rw [dite_eq_left hβ]; rfl
  obtain ⟨-, ⟨-, -, hlift', hconv'⟩, hX'⟩ := id hr'
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (Formalism.L2.SG.Pf.IsLift_mapL (g⁻¹ * g') hβ _ _).2 hlift'
    rw [hmap, ← hmapL] at h1
    exact h1
  · exact GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS _ (gS D) (gS_pos D) _ _
      (fun P hP a => frame_mem_locP _ _ hr P hP a)
      (fun P hP => GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP)
  · exact GlobalTheory.FrameIsom.frameOK_mapLF D (g⁻¹ * g') hβ _ _ hmap _ _ ⟨hconv', hX'⟩

end GlobalTheory.Unfold.AdmGlued
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedTermFrameAdmissibleIntegralStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedTerm_frame_admissibleIntegral : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D (X.Fu u)) u' (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) := by
  first | exact @GlobalTheory.Unfold.AdmGlued.glued_frame_PD | exact GlobalTheory.Unfold.AdmGlued.glued_frame_PD | (intros; apply GlobalTheory.Unfold.AdmGlued.glued_frame_PD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTerms

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowTermReal

variable {D : D7}

theorem gmap_one' (L : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) L = L := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul' (a b : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) :
    Xflag F i ≤ Xflag F j :=
  Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => show a.1 < j by omega)

theorem adapt_map_xflag {T : D.host.E} {g : GV D} {A B : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g A B)
    (j : ℕ) {x : (VS D).V} (hx : x ∈ Xflag A j) : g x ∈ Xflag B j := by
  change x ∈ Submodule.span D.host.E (A.fl.e '' {i | i.1 < j}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : a.1 < j := ha
    have h1 := hg.2 a.castSucc
    have e1 : frame A a.castSucc = A.fl.e a := by simp [frame, FlagG.fvec]
    have e2 : frame B a.castSucc = B.fl.e a := by simp [frame, FlagG.fvec]
    rw [e1, e2, Fin.val_castSucc] at h1
    have h2 : B.fl.e a ∈ Xflag B j := Submodule.subset_span ⟨a, ha', rfl⟩
    have h3 := xflag_mono B (le_of_lt ha') h1
    simpa using add_mem h3 h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem adapt_mul {T : D.host.E} {g h : GV D} {A B C : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g B C)
    (hh : Adapt h A B) : Adapt (g * h) A C := by
  refine ⟨mul_mem hg.1 hh.1, fun a => ?_⟩
  have e : (g * h) (frame A a) - frame C a =
      g (h (frame A a) - frame B a) + (g (frame B a) - frame C a) := by
    simp only [mul_apply_eq_comp, map_sub]; abel
  rw [e]
  exact add_mem (adapt_map_xflag hg _ (hh.2 a)) (hg.2 a)

theorem adapt_of_nlam {T : D.host.E} {Λ : LV D} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D}
    (hn : n ∈ NLam Λ F) : Adapt n F F := by
  refine ⟨hn.1.1, fun a => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [hz, Fin.val_last]
    have hzo : F.fl.z ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      change x ∈ Submodule.span D.host.E (Set.range F.fl.e) at hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
      | smul c x _ hx => simp [hx]
    have hX : Xsp F ≤ Xflag F D.R.rS :=
      Submodule.span_mono fun _ ⟨i, h⟩ => ⟨i, i.2, h⟩
    exact hX (hn.2.2 _ hzo)
  · have hi : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [hi, Fin.val_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem frame_mapLF' {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {g : GV D}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (a : Fin (D.R.rS + 1)) : frame (mapLF g F) a = g (frame F a) := by
  simp only [mapLF, dite_eq_left hg, frame, FlagG.fvec, mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp

end GlobalTheory.RowTermReal

namespace GlobalTheory.RowTermReal

theorem rowLat_first {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u)) F ∧ IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u) (D.mem u).A.T_prime.ne_zero (X.Fu u) F Z
    (fun p => (FP p).A) (fun p => (hB p).1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L, (y p).hL, hlat.symm.trans hn.2.2⟩)

theorem rowLat_second {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u')) F' ∧ IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u') (D.mem u').A.T_prime.ne_zero (X.Fu u') F' Z
    (fun p => (FP p).B) (fun p => (hB p).2.1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L', (y p).hL', hlat.symm.trans hn.2.2⟩)

theorem exists_term_of_locOver : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL
  obtain ⟨g0, hg0, hrow0⟩ := rowLat_first X F F' Z FP hB Λ y hL
  obtain ⟨g0', hg0', hrow0'⟩ := rowLat_second X F F' Z FP hB Λ y hL
  obtain ⟨Λ₁, hΛ₁, σ, hσ, hσΛ⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u u).1 _ hrow0
  obtain ⟨Λ₁', hΛ₁', σ', hσ', hσΛ'⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u' u').1 _ hrow0'
  have hg : Adapt (g0 * σ) (lf D (X.Fu u)) F := adapt_mul hg0 hσ
  have hg' : Adapt (g0' * σ') (lf D (X.Fu u')) F' := adapt_mul hg0' hσ'
  have hgΛ : Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ = Λ₁ := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
  have hgΛ' : Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ = Λ₁' := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
  have hrow : IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ) := hgΛ ▸ (Y.rowsOK u).1 Λ₁ hΛ₁
  have hrow' : IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ) := hgΛ' ▸ (Y.rowsOK u').1 Λ₁' hΛ₁'
  have hPD := GlobalTheory.T.gluedTerm_frame_admissibleIntegral D X Y u u' F F' w hw hG Z FP hB hR Λ y hL _ _ hg hg' hrow hrow'
  rw [hgΛ] at hPD
  set g := g0 * σ with hgdef
  set g' := g0' * σ' with hg'def
  have hγ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg.1) hg'.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') Λ₁' = Λ₁ := by
    rw [← hgΛ, ← hgΛ', gmap_mul', ← gmap_mul' g' g'⁻¹, mul_inv_cancel, gmap_one']
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X (g⁻¹ * g') hγ
  let p : GCar X u u' (X.Fu u) (X.Fu u') Λ₁ Λ₁' := ⟨(x, g⁻¹ * g'), hx, hγ, hγΛ, hPD⟩
  let t : TauC Y u u' := ⟨Λ₁, hΛ₁, Λ₁', hΛ₁', Quot.mk _ p⟩
  refine ⟨t, ?_⟩
  obtain ⟨n, hn, n', hn', hrel⟩ := Formalism.L2.SG.Pf.SatGramRep.grel_rep t p rfl
  have hlin : t.lin = n⁻¹ * (g⁻¹ * g') * n'⁻¹ := by
    have h : g⁻¹ * g' = n * t.lin * n' := hrel
    rw [h]; group
  refine ⟨g * n, adapt_mul hg (adapt_of_nlam hn), ?_, ?_⟩
  · have hA : Adapt (g' * n'⁻¹) (lf D (X.Fu u')) F' :=
      adapt_mul hg' (adapt_of_nlam (Formalism.L2.SG.Pf.nlam_inv hn'))
    have htl : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
    have e : g * n * t.lin = g' * n'⁻¹ := by rw [hlin]; group
    refine ⟨mul_mem hg.1 hn.1.1, fun a => ?_⟩
    show (g * n) (frame (mapLF t.lin (lf D (X.Fu u'))) a) - frame F' a ∈ _
    rw [frame_mapLF' _ htl, ← mul_apply_eq_comp, e]
    exact hA.2 a
  · show Λ = Formalism.HermitianLatticesTheory.gmap (g * n) Λ₁
    have hn1 : Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₁ := hn.1.2
    rw [gmap_mul', hn1, ← hgΛ, ← gmap_mul', mul_inv_cancel, gmap_one']

end GlobalTheory.RowTermReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTermsStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowTerm_of_local_completions_terms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  first | exact @GlobalTheory.RowTermReal.exists_term_of_locOver | exact GlobalTheory.RowTermReal.exists_term_of_locOver | (intros; apply GlobalTheory.RowTermReal.exists_term_of_locOver <;> assumption)
end
end
