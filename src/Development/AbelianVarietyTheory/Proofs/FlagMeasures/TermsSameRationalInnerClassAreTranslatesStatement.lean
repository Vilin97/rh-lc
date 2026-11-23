module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerLatticeIdentificationCompatOfGraphEqStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentFrameAdaptedAndInvMemStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesEqOfAdaptedIsometryInnerLatticesEqStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryMapFlagSpaces

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem adapt_map_flag (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D) (hg : Adapt g F G) :
    (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧
      (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  have hmono : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b := by
    intro H a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))
  have hmem : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j := by
    intro H i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hX : ∀ H : LFlag (D.sp.Y 0) D.R.rS T, Xsp H = Xflag H D.R.rS := by
    intro H
    show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})
    congr 1
    ext x
    simp
  have hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1 := by
    intro i
    have := hg.2 i.castSucc
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
    intro j
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    show g (F.fl.e i) ∈ Xflag G j
    have h1 := hmono G (le_of_lt hi) (hstep i)
    have h2 := hmem G i hi
    simpa using add_mem h1 h2
  have hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    induction j with
    | zero =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.map_mono (hmono F (Nat.le_succ j))
      have h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        hmap (ih (hmono G hi' (hstep i)))
      have h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.mem_map_of_mem (hmem F i hi)
      have h3 := sub_mem h2 h1
      simp only [LinearEquiv.coe_coe, sub_sub_cancel] at h3
      exact h3
  refine ⟨fun j => le_antisymm (hle j) (hge j), ?_⟩
  rw [hX F, hX G]
  exact le_antisymm (hle _) (hge _)

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryMapFlagSpacesStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces : ∀ (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F G → (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧ (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  first | exact @GlobalTheory.adapt_map_flag | exact GlobalTheory.adapt_map_flag | (intros; apply GlobalTheory.adapt_map_flag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRightChangeMovesFlagComplement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnipRight

theorem Xflag_eq_Xsp {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : LFlag S r T) {j : ℕ} (hj : r ≤ j) : Xflag F j = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, lt_of_lt_of_le i.2 hj, h⟩⟩

theorem map_Xsp_NRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D) (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F := by
  have hle : (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xsp F := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x ∈ Xflag F (D.R.rS + 1) := by rw [Xflag_eq_Xsp F (by omega)]; exact hx
    have h2 := hn.2.1 D.R.rS x h1
    rw [Xflag_eq_Xsp F le_rfl] at h2
    have := (Xsp F).add_mem h2 hx
    simpa using this
  haveI : FiniteDimensional D.host.E (Xsp F) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq n (Xsp F))

theorem Xsp_mapLF' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem unip_right : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ m n' : GV D),
    γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' →
      ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  intro D T' F' γ₁ γ₂ m n' h1 hm hn hγ x' hx'
  have h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [hγ]; exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hm h1) hn.1
  set y := γ₁.symm x' with hy
  have hyo : y ∈ orth (VS D) (Xsp F') := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx' ⊢
    intro z hz
    have hz' : γ₁ z ∈ Xsp (mapLF γ₁ F') := by
      rw [Xsp_mapLF' γ₁ h1]; exact ⟨z, hz, rfl⟩
    have := hx' (γ₁ z) hz'
    rw [← h1 z y, hy]
    simpa using this
  have hd : n' y - y ∈ Xsp F' := hn.2.2 y hyo
  have hd' : y - n' y ∈ Xsp F' := by
    have := (Xsp F').neg_mem hd; simpa using this
  rw [← map_Xsp_NRat F' n' hn] at hd'
  obtain ⟨w, hw, hwe⟩ := hd'
  rw [Xsp_mapLF' γ₂ h2]
  refine ⟨w, hw, ?_⟩
  have hx'y : x' = γ₁ y := by simp [hy]
  show γ₂ w = m x' - (γ₂ * γ₁⁻¹) x'
  rw [hγ, hx'y]
  simp only [LinearEquiv.mul_apply]
  have hinv : γ₁⁻¹ (γ₁ y) = y := by
    show γ₁.symm (γ₁ y) = y
    simp
  have hwe' : n' w = y - n' y := hwe
  rw [hinv, hwe', map_sub, map_sub]

end GlobalTheory.UnipRight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRightChangeMovesFlagComplementStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_right_change_moves_flag_complement : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ m n' : GV D), γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' → ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  first | exact @GlobalTheory.UnipRight.unip_right | exact GlobalTheory.UnipRight.unip_right | (intros; apply GlobalTheory.UnipRight.unip_right <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslates

section

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem gmap_inv_of {a : GV D} {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap a M = N) : Formalism.HermitianLatticesTheory.gmap a⁻¹ N = M := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem adapt_mul {T : D.host.E} {F G H : LFlag (D.sp.Y 0) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have hmap := (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D T G H g' hg').1 a.val
  have h1 : g' (g (frame F a) - frame G a) ∈ Xflag H a.val := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (hg.2 a)
  have h2 := hg'.2 a
  have e : (g' * g) (frame F a) - frame H a =
      g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    rw [map_sub, LinearEquiv.mul_apply]
    abel
  rw [e]
  exact add_mem h1 h2

theorem adapt_fix {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) : Adapt h F F := by
  refine ⟨hi, fun a => ?_⟩
  rw [hf a, sub_self]
  exact zero_mem _

theorem frame_mapLF {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (a : Fin (D.R.rS + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  simp only [frame, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.fvec]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
    rfl
  · simp only [Fin.snoc_castSucc]
    rfl

theorem xsp_mapLF {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Xsp, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem adapt_mapLF {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {γ g : GV D}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) : Adapt g (mapLF γ F) G ↔ Adapt (g * γ) F G := by
  simp only [Adapt, frame_mapLF F hγ, LinearEquiv.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem h1 hγ, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := mul_mem h1 (inv_mem hγ)
    rwa [mul_inv_cancel_right] at this

end GlobalTheory.Unfold.CntC

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem translates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' ∧ ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t₀.lam (a * t₀.lin * a'⁻¹) t.lin := by
  intro D X Y u u' F F' w _ _ t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨g₀, hg₀a, hg₀b, rfl⟩ := h₀
  obtain ⟨ψ₁, hψ₁a, hψ₁b, rfl⟩ := h₁
  obtain ⟨h, ⟨hhi, hhF, hhF'⟩, hgd⟩ := hR
  rw [← gmap_mul] at hgd
  set ψ₀ := h * g₀ with hψ₀
  have hψ₀a : Adapt ψ₀ (lf D (X.Fu u)) F := adapt_mul hg₀a (adapt_fix hhi hhF)
  have hψ₀b : Adapt ψ₀ t₀.frame F' := adapt_mul hg₀b (adapt_fix hhi hhF')
  have li₀ : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have lg₀ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have li : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have lg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F := congrArg Prod.fst hgd
  have e2 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F' = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F' :=
    congrArg (fun x => x.2.1) hgd
  have e3 : (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam)).2.2 = (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam)).2.2 :=
    congrArg (fun x => x.2.2) hgd
  obtain ⟨hlam, n, hn, hA⟩ := GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq D X Y u F ψ₀ ψ₁ t₀.lam t.lam t₀.mem t.mem hψ₀a hψ₁a e1
  have hψ₀b' : Adapt (ψ₀ * t₀.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₀) li₀).1 hψ₀b
  have hψ₁b' : Adapt (ψ₁ * t.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁) li).1 hψ₁b
  have q₀ : Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam' = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam :=
    (gmap_mul ψ₀ t₀.lin t₀.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₀) lg₀)
  have q₁ : Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam' = Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam :=
    (gmap_mul ψ₁ t.lin t.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₁) lg)
  have e2' : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam') F' = Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam') F' := by
    rw [q₀, q₁]
    exact e2
  obtain ⟨hlam', n', hn', hA'⟩ :=
    GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq D X Y u' F' (ψ₀ * t₀.lin) (ψ₁ * t.lin) t₀.lam' t.lam' t₀.mem' t.mem' hψ₀b' hψ₁b' e2'
  refine ⟨hlam, hlam', n * (ψ₁⁻¹ * ψ₀), hA, n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)), hA', ?_⟩
  have hA2 : Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀)) t₀.lam = t₀.lam := hA.2
  have hA'2 : Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam' = t₀.lam' := hA'.2
  have hγ : n * (ψ₁⁻¹ * ψ₀) * t₀.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))⁻¹ = n * t.lin * n'⁻¹ := by
    group
  have hβ : t.lin * (n * t.lin * n'⁻¹)⁻¹ =
      t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by
    group
  rw [hγ]
  have hnN := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n hn
  have hn'N := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n' hn'
  have hn'iN := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n'⁻¹ hn'N.2
  have hni : n⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hnN.2.1
  have hn'i : n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn'N.2.1
  have hni' : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1
  have hγi : n * t.lin * n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hni' li) hn'i
  unfold KeyEq
  refine ⟨⟨n⁻¹, hnN.2, n', hn', by group⟩, ?_⟩
  have hΨ₀a : Adapt (ψ₁ * n⁻¹) (lf D (X.Fu u)) F := adapt_mul (GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n⁻¹ hnN.2).1 hψ₁a
  have hΨ₀b : Adapt (ψ₁ * n⁻¹) (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u'))) F' := by
    refine (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁ * n⁻¹) hγi).2 ?_
    have : ψ₁ * n⁻¹ * (n * t.lin * n'⁻¹) = ψ₁ * t.lin * n'⁻¹ := by group
    have key := adapt_mul hn'iN.1 hψ₁b'
    rw [← this] at key
    exact key
  have hg1 : Formalism.HermitianLatticesTheory.gmap (ψ₁ * n⁻¹) t₀.lam = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam := by
    have : ψ₁ * n⁻¹ = ψ₀ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by group
    rw [this, gmap_mul, gmap_inv_of hA2]
  refine GlobalTheory.T.innerLatticeIdentification_compat_of_graph_eq D _ _ (lf D (X.Fu u)) F (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u')))
    (mapLF t.lin (lf D (X.Fu u'))) F' t₀.lam (ψ₁ * n⁻¹) ψ₁ (t.lin * (n * t.lin * n'⁻¹)⁻¹)
    (mul_mem hψ₁a.1 hni) hψ₁a.1 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀a).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hψ₁a).2
    (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀b).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ (mapLF t.lin (lf D (X.Fu u'))) F' ψ₁ hψ₁b).2
    ?_ (mul_mem li (inv_mem hγi)) ?_ ?_ ?_ ?_
  · exact (congrArg (fun Λ => (gdat F F' Λ).2.2) hg1).trans
      (e3.trans (congrArg (fun Λ => (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2) hlam))
  · calc Formalism.HermitianLatticesTheory.gmap (t.lin * (n * t.lin * n'⁻¹)⁻¹) t₀.lam
          = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹) t₀.lam :=
            congrArg (fun g => Formalism.HermitianLatticesTheory.gmap g t₀.lam) hβ
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) (Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀))⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) t₀.lam :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹)) (gmap_inv_of hA2)
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) (Formalism.HermitianLatticesTheory.gmap t₀.lin⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) t₀.lam' :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))))) (gmap_inv_of lg₀)
      _ = Formalism.HermitianLatticesTheory.gmap t.lin (Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam') := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' := congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hA'2
      _ = t₀.lam := (congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hlam'.symm).trans (lg.trans hlam)
  · rw [xsp_mapLF _ hγi, xsp_mapLF _ li, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    exact congrArg (fun g : GV D => g x) (inv_mul_cancel_right t.lin (n * t.lin * n'⁻¹))
  · intro l hl
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := hnN.2.2.2 l (Submodule.mem_inf.mp hl).2
    rw [← this] at key
    exact key
  · intro x' hx'
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := GlobalTheory.T.unipotent_right_change_moves_flag_complement D _ (lf D (X.Fu u')) (n * t.lin * n'⁻¹) t.lin n⁻¹ n' hγi hni hn' (by group) x'
      (Submodule.mem_inf.mp hx').2
    rw [← this] at key
    exact key

end GlobalTheory.Unfold.CntC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslatesStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.terms_same_rational_inner_class_are_translates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' ∧ ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t₀.lam (a * t₀.lin * a'⁻¹) t.lin := by
  first | exact @GlobalTheory.Unfold.CntC.translates | exact GlobalTheory.Unfold.CntC.translates | (intros; apply GlobalTheory.Unfold.CntC.translates <;> assumption)
end
end
