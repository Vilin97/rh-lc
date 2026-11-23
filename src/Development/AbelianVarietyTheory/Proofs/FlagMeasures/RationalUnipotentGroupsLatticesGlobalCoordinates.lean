module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnipotentFrameCorrespondsUnderIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PiTensorProduct
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToDeterminesUnipotentFactorisationStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentConjIffOfUnitriangularIsometry
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinates

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.HL.placesLat_gcoordLat_eq : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  intro D Z T T' F0 F0' FP G c σ p g Λ hE
  unfold GlobalTheory.HL.GCoord.lat GlobalTheory.HL.Places.lat GlobalTheory.HL.WCoord.lat Formalism.MainNotions.S.LocNG.img Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g (baseChange₂ D p x), ⟨baseChange₂ D p x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    show (c.c p).e (g (baseChange₂ D p x)) = (placesOf Z).bc p (c.e (σ x))
    rw [hE x, c.compat p (σ x)]
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨c.e (σ x), ⟨x, hx, rfl⟩, ?_⟩
    show (placesOf Z).bc p (c.e (σ x)) = (c.c p).e (g (baseChange₂ D p x))
    rw [hE x, c.compat p (σ x)]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinatesStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completion_moved_lattice_eq_local_coordinates : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.HL.placesLat_gcoordLat_eq | exact GlobalTheory.HL.placesLat_gcoordLat_eq | (intros; apply GlobalTheory.HL.placesLat_gcoordLat_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRationalUnipotentOfLocalExtension

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocReflect

variable {D : D7}

theorem mem_of_baseChange_mem_span (p : PlF D) (W : Submodule D.host.E (VS D).V) {y : (VS D).V}
    (hy : baseChange₂ D p y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V))) : y ∈ W := by
  by_contra hyW
  obtain ⟨φ, hφy, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyW inferInstance
  let ψ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun v => ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * v i
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  have hψ : ∀ x, ψ (baseChange₂ D p x) = (D.s.atP p).ιE (φ x) := by
    intro x
    show ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * (D.s.atP p).ιE ((VS D).frame.repr x i) = _
    conv_rhs => rw [← (VS D).frame.sum_repr x]

    simp only [map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hle : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V)) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    show ψ (baseChange₂ D p w) = 0
    rw [hψ]
    have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
    rw [hφW, Submodule.mem_bot] at this
    rw [this, map_zero]
  have h0 : ψ (baseChange₂ D p y) = 0 := hle hy
  rw [hψ] at h0
  exact hφy ((map_eq_zero_iff _ (RingHom.injective (D.s.atP p).ιE)).1 h0)

theorem span_scaled_le (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (S : Set (Fin D.R.rS)) :
    Submodule.span (D.s.atP p).Ep ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' S) ≤
      Submodule.span (D.s.atP p).Ep
        (baseChange₂ D p '' ((Submodule.span D.host.E (F.fl.e '' S) : Submodule D.host.E (VS D).V) : Set (VS D).V)) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  show frFac Z.δ p b.castSucc • baseChange₂ D p (frame F b.castSucc) ∈ _
  rw [GlobalTheory.LocExt.frame_castSucc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩)

theorem mem_nrat_of_ext : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p),
    GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  intro D Z p T F γ g hE hN
  obtain ⟨hU, hfl, hperp⟩ := hN
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply RingHom.injective (D.s.atP p).ιE
    show (D.s.atP p).ιE (brS (VS D) (γ y) (γ x)) = (D.s.atP p).ιE (brS (VS D) y x)
    rw [← baseChangeAt_form Z.M p (Z.hcj p), ← baseChangeAt_form Z.M p (Z.hcj p), ← hE, ← hE]
    exact hU (baseChange₂ D p y) (baseChange₂ D p x)
  · intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : a.1 < j + 1 := ha
      have h1 := hfl a
      have e : g (scaled Z p (frame F) a.castSucc) - scaled Z p (frame F) a.castSucc =
          frFac Z.δ p a.castSucc • baseChange₂ D p (γ (F.fl.e a) - F.fl.e a) := by
        simp only [scaled, GlobalTheory.LocExt.frame_castSucc, map_smul, hE (F.fl.e a), map_sub, smul_sub]
      rw [e] at h1
      obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a.castSucc
      have h2 := Submodule.smul_mem _ ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) (span_scaled_le Z p F {b | b < a} h1)
      rw [← hu, smul_smul, Units.inv_mul, one_smul] at h2
      have h3 := mem_of_baseChange_mem_span p _ h2
      exact GlobalTheory.FlagChange.Xa_mono F.fl (Nat.lt_succ_iff.1 ha') h3
    | zero => simp
    | add x y _ _ ihx ihy =>
      have e : γ (x + y) - (x + y) = (γ x - x) + (γ y - y) := by rw [map_add (f := _)]; abel
      rw [e]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
      rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ ih
  · intro x hx
    have hb : baseChange₂ D p x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨a, rfl⟩ := hu
        show (locH Z p).h (baseChange₂ D p x) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) = 0
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]
        have h0 : (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0 := by
          show LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0
          rw [baseChangeAt_form Z.M p (Z.hcj p), GlobalTheory.LocExt.frame_castSucc]
          show (D.s.atP p).ιE ((VS D).hT (F.fl.e a) x) = 0
          rw [GlobalTheory.FlagChange.mem_orth_X.1 hx (F.fl.e a) (GlobalTheory.FlagChange.e_mem_X F.fl a), map_zero]
        rw [h0, mul_zero]
      | zero =>
        rw [(locH Z p).h_herm, (locH Z p).h_zero_left, map_zero]
      | add u v _ _ ihu ihv =>
        rw [(locH Z p).h_herm, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm, ← (locH Z p).h_herm, ihu, ihv,
          add_zero]
      | smul c u _ ih =>
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm, ih, mul_zero]
    have h2 := hperp _ hb
    rw [hE, ← map_sub] at h2
    have h3 : baseChange₂ D p (γ x - x) ∈ Submodule.span (D.s.atP p).Ep
        ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' Set.univ) := by
      rw [Set.image_univ]; exact h2
    have h4 := mem_of_baseChange_mem_span p _ (span_scaled_le Z p F Set.univ h3)
    rw [Set.image_univ] at h4
    exact h4

end GlobalTheory.LocReflect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRationalUnipotentOfLocalExtensionStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_rationalUnipotent_of_local_extension : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  first | exact @GlobalTheory.LocReflect.mem_nrat_of_ext | exact GlobalTheory.LocReflect.mem_nrat_of_ext | (intros; apply GlobalTheory.LocReflect.mem_nrat_of_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentConjIffOfUnitriangularIsometryStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (D.sp.Y 0) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) → ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  first | exact @GlobalTheory.FlagMove.nrat_conj_iff | exact GlobalTheory.FlagMove.nrat_conj_iff | (intros; apply GlobalTheory.FlagMove.nrat_conj_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinates

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GrpCoord

theorem rat_iff (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G)
    {T₁ : D.host.E} (F₁ : LFlag (D.sp.Y 0) D.R.rS T₁) (g : ∀ p, Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ p a, g p a = (c.c p).e (scaled Z p (frame F₁) a)) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    γ ∈ NRat F₁ ↔ (c.e.symm.trans γ).trans c.e ∈ (placesOf Z).rat (fun p => (G.S p).Nof (g p)) := by
  have hgf : ∀ p, g p = fun a => (c.c p).e (scaled Z p (frame F₁) a) := fun p => funext (hg p)
  constructor
  · intro hγ p
    obtain ⟨h, hext, -, -, -, hNU⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ.1
    let k := ((c.c p).e.symm.trans h).trans (c.c p).e
    have hk : k ∈ (G.S p).Nof (g p) := by
      rw [hgf p]; exact (GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p) _ h).1 (hNU F₁ hγ)
    refine ⟨k, hk, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := c.e.surjective x
      have h1 : (placesOf Z).bc p (c.e y) = (c.c p).e (baseChange₂ D p y) := (c.compat p y).symm
      have h2 : ((c.e.symm.trans γ).trans c.e) (c.e y) = c.e (γ y) := by simp
      rw [h2, h1, ← c.compat p (γ y), ← hext y]
      show (c.c p).e (h ((c.c p).e.symm ((c.c p).e (baseChange₂ D p y)))) = _
      rw [LinearEquiv.symm_apply_apply]
  · intro hγ
    have hne : Nonempty (PlF D) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField _)⟩⟩
    obtain ⟨p⟩ := hne
    obtain ⟨g₀, hg'N, hg'E⟩ := hγ p
    let g' : type_of% ((c.c p).e.symm.trans (c.c p).e) := g₀
    let h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p := ((c.c p).e.trans g').trans (c.c p).e.symm
    have hconj : ((c.c p).e.symm.trans h).trans (c.c p).e = g' := by
      ext x; simp [h]
    have hN : h ∈ NU (locH Z p) (scaled Z p (frame F₁)) := by
      rw [GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p), hconj, ← hgf p]; exact hg'N
    refine GlobalTheory.T.mem_rationalUnipotent_of_local_extension D Z p F₁ γ h ?_ hN
    intro y
    have h1 : (c.c p).e (baseChange₂ D p y) = (placesOf Z).bc p (c.e y) := c.compat p y
    have h3 : g₀ ((placesOf Z).bc p (c.e y)) = (placesOf Z).bc p (c.e (γ y)) :=
      (hg'E _).trans (by simp)
    show (c.c p).e.symm (g₀ ((c.c p).e (baseChange₂ D p y))) = baseChange₂ D p (γ y)
    rw [h1, h3, ← c.compat p (γ y), LinearEquiv.symm_apply_apply]

theorem grp_eq {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp σ n = (c.e.symm.trans (σ * n * σ⁻¹)).trans c.e := by
  ext x; simp [GCoord.grp]

theorem frame_mapLF (D : D7) {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) : frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF; rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast b => simp [frame, FlagG.fvec, mapFlag]

theorem grp_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (∀ n, n ∈ NRat (lf D (X.Fu u)) ↔ c.grp ρ n ∈ G.N) ∧ (∀ m, m ∈ NRat (lf D (X.Fu u')) ↔ c.grp (ρ * t₀.lin) m ∈ G.N') ∧ (∀ (σ n : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) Λ, c.lat (σ * n) Λ = (c.lat σ Λ).map (((c.grp σ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) ∧ (∀ (σ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (x : G.GLV), ∃ n, c.grp σ n = x) ∧ (∀ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∀ (p : PlF D) g Λ, GlobalTheory.LocOver.Ext p σ g → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Y.M p) g (lattice₂ D Y.M p Λ))) ∧ ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hAB G c t₀ ρ U U' hmv
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := hmv
  have hN : G.N = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F00) a))) := by
    unfold GFrames.N Frames.N
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f_eq, (hAB p).1.1]
  have hN' : G.N' = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F'0) a))) := by
    unfold GFrames.N' Frames.N'
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f'_eq, (hAB p).1.2.1]
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  refine ⟨fun n => ?_, fun m => ?_, fun σ n Λ => ?_, fun σ x => ?_, fun σ _ p g Λ hg => ?_, ?_⟩
  · refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F00 ρ U hρ hU hF n).trans ?_
    rw [grp_eq, hN]
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · have hF2 : ∀ b, (ρ * t₀.lin) (frame (lf D (X.Fu u')) b) = ∑ a, U' a b • frame F'0 a := by
      intro b
      rw [← hF' b]
      show ρ (t₀.lin _) = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) b)
      rw [frame_mapLF D _ hlin]
    refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F'0 (ρ * t₀.lin) U' (Subgroup.mul_mem _ hρ hlin) hU' hF2 m).trans ?_
    rw [grp_eq, hN']
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · unfold GCoord.lat
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp [GCoord.grp]
  · refine ⟨((σ.trans c.e).trans x).trans (σ.trans c.e).symm, ?_⟩
    ext y; simp [GCoord.grp]
  · exact GlobalTheory.T.completion_moved_lattice_eq_local_coordinates D _ F00 F'0 FP G c σ p g Λ hg
  · exact GlobalTheory.T.moves_to_determines_unipotent_factorisation D X Y u u' F00 F'0 t₀ ρ U U' ⟨hρ, hU, hU', hF, hF'⟩

end GlobalTheory.HL.GrpCoord
end
end
end
