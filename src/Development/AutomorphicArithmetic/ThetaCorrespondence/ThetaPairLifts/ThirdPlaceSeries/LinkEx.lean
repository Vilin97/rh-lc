module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.PeriodIntegrals.MinkowskiQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosedRankTiesFC2S

section

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.Ext.Lw
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct
theorem rankTiesF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  obtain ⟨T⟩ := h x e1 ((le_max_left _ _).trans hx) i
  exact mu0Tie_of_sym T.cols u
theorem second_chern_linked_closed_rank_ties : Closed _root_.Formalism.L2.SecondChernLinkedClass fun Fm _ => RankTiesF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩
end Formalism.MainNotions.Ext.Lw
end
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice

section

@[expose] public section

namespace PI.MkQ

open Matrix

variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))

def orbitSet : Set (Fin N → ℚ) :=
  Set.range fun p : G × Fin N =>
    ((p.1 : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single p.2 1)

def lat : Submodule ℤ (Fin N → ℚ) := Submodule.span ℤ (orbitSet G)

theorem single_mem (i : Fin N) : (Pi.single i 1 : Fin N → ℚ) ∈ lat G := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  show (((1 : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
    Pi.single i 1
  exact Matrix.one_mulVec _

theorem mulVec_mem (g : G) {v : Fin N → ℚ} (hv : v ∈ lat G) :
    ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v ∈ lat G := by
  have hv' : v ∈ Submodule.span ℤ (orbitSet G) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    show (((g * h : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ
        (((h : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec]
    rfl
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

noncomputable def rho : G →* Module.End ℤ (lat G) where
  toFun g := ((((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVecLin).restrictScalars
    ℤ).restrict (fun v hv => mulVec_mem G g hv)
  map_one' := by ext v i; simp
  map_mul' g g' := by
    ext v : 1
    apply Subtype.ext
    show _ = ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec
      (((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (v : Fin N → ℚ))
    simp [Matrix.mulVec_mulVec]

theorem rho_apply_coe (g : G) (v : lat G) :
    ((rho G g v : lat G) : Fin N → ℚ) =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v := rfl

section finite

variable [Finite G]

theorem orbitSet_finite : (orbitSet G).Finite := Set.finite_range _

instance : Module.Finite ℤ (lat G) := Module.Finite.span_of_finite ℤ (orbitSet_finite G)

instance : Module.IsTorsionFree ℤ (lat G) := inferInstance

instance : Module.Free ℤ (lat G) := Module.free_of_finite_type_torsion_free'

theorem card_basis : Fintype.card (Module.Free.ChooseBasisIndex ℤ (lat G)) = N := by
  classical
  apply le_antisymm
  · have h1 : LinearIndependent ℤ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (Module.Free.chooseBasis ℤ (lat G)).linearIndependent.map' (lat G).subtype
        (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℚ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h1
    simpa using h2.fintype_card_le_finrank
  · have h3 : LinearIndependent ℚ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) := by
      have h7 := (Pi.basisFun ℚ (Fin N)).linearIndependent
      rwa [show ⇑(Pi.basisFun ℚ (Fin N)) = fun i : Fin N => (Pi.single i 1 : Fin N → ℚ) from
        funext fun i => by simp] at h7
    have h4 : LinearIndependent ℤ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).2 h3
    have h5 : LinearIndependent ℤ (fun i : Fin N => (⟨Pi.single i 1, single_mem G i⟩ : lat G)) :=
      LinearIndependent.of_comp (lat G).subtype h4
    have h6 := h5.fintype_card_le_finrank
    rw [Module.finrank_eq_card_chooseBasisIndex] at h6
    simpa using h6

noncomputable def basisFin : Module.Basis (Fin N) ℤ (lat G) :=
  (Module.Free.chooseBasis ℤ (lat G)).reindex (Fintype.equivFinOfCardEq (card_basis G))

noncomputable def phi : G →* GeneralLinearGroup (Fin N) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisFin G)).toRingEquiv.toMonoidHom).comp
    (rho G).toHomUnits

theorem phi_injective : Function.Injective (phi G) := by
  intro g g' h
  have h1 : rho G g = rho G g' := by
    have h0 := congrArg (fun u : GeneralLinearGroup (Fin N) ℤ => (u : Matrix (Fin N) (Fin N) ℤ)) h
    change (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g) =
      (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g') at h0
    exact (LinearMap.toMatrixAlgEquiv (basisFin G)).injective h0
  have h2 : ∀ i, ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) =
      ((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) := by
    intro i
    have h0 := congrArg
      (fun f : Module.End ℤ (lat G) => ((f ⟨Pi.single i 1, single_mem G i⟩ : lat G) : Fin N → ℚ)) h1
    simpa [rho_apply_coe] using h0
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h0 := congrFun (h2 b) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0

end finite

theorem minkowskiBoundQ : PI.MinkowskiBoundQ := by
  intro N G hG
  let e := MonoidHom.ofInjective (phi_injective G)
  have : Finite (phi G).range := Finite.of_equiv _ e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact card_dvd_minkowskiNumber N _ inferInstance

end PI.MkQ
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ

section

@[expose] public section

theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEx

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin : ∀ (𝒜 : FamClass)
    (cT : ℝ → ℝ → ℝ)
    (hEx : MinkDiv → DesignChoices (WithTw 𝒜) 3 cT)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLit : LitThin), DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 := by
  intro 𝒜 cT hEx sel hduty hTu hn4 hLit
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN 𝒜)) Fm → 𝒜 Fm := fun _ hc => hc.1.1.1
  have hProv : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ChosenProviso Fm 3 :=
    (hn4.and (Pk.Closed.sub _root_.Formalism.MainNotions.Ext.Lw.second_chern_linked_closed_rank_ties fun Fm hc => (hRec Fm (hsub Fm hc)).c2s)).imp
      fun Fm _ _ h => Formalism.MainNotions.StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 hCe h.1 h.2
  have hE' : DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 :=
    designExists_of_choices (designChoices_upN (hEx minkowski_bound_rat)) hTu hProv
      (chosenThin_closed (WithTw (WithSm (WithChN 𝒜))) hLit)
  exact hE'
end
end
end
end
