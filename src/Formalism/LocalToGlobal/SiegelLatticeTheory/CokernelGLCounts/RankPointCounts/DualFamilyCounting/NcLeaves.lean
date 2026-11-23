module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArith
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcGlob
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AnisotropicComplementDefinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanInvariantsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegenerateOnOrthCompl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IsomFixIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanRankOneLine
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GluedLatticeMassFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GluedExists

section

@[expose] public section

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glued_exists {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t)
    (hk2 : 2 ≤ finrank K (wPerp h1 z))
    (hU0 : ∃ Λ₀ : Submodule (𝓞 K) V1, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 Λ₀) :
    ∃ M, IsGlueLat h1 z M := by
  have hH' := hH
  obtain ⟨hK, hF, hsym, hzz, ht, hd⟩ := hH'
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  have hz : z ≠ 0 := z_ne_zero hz0
  have hC : IsCompl (Submodule.span K {z}) (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    exact isCompl_span hz0
  have hP : Formalism.L2.SG.Pf.Cnt.PosDefOn h1 (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    intro x hx hx0 φ
    exact hd ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h)) φ
  have hLat : Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) :=
    ⟨Submodule.fg_span_singleton z, Submodule.span_span_of_tower (𝓞 K) K {z}⟩
  have hInt : Formalism.HermitianLatticesTheory.IsIntegralLat h1 (Submodule.span (𝓞 K) {z}) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hzz]
    obtain ⟨c, hc⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range (K := K) a
    rw [← hc]
    refine Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem c)
      (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) ?_)
    rw [Submodule.mem_one]
    exact ⟨-((t : ℕ) : 𝓞 K), by simp⟩
  have hcJ : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭 <
        finrank K (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    intro 𝔭 h𝔭
    rw [orthK_span]
    have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
    obtain ⟨-, e2⟩ := Formalism.L2.SG.Pf.G9.vJ_cJ_eq Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds hK hF hsym hLat h𝔭
      (jordan_rank_one_line hzz ht hz 𝔭)
    rw [e2]
    have hle : Formalism.L2.SG.Pf.Cnt.cJof 𝔭
        (fun _ : Fin (finrank K (Submodule.span K {z})) => -((t : ℕ) : 𝓞 F)) ≤ 1 := by
      unfold Formalism.L2.SG.Pf.Cnt.cJof
      calc _ ≤ (Finset.univ : Finset (Fin (finrank K (Submodule.span K {z})))).card :=
            Finset.card_filter_le _ _
        _ = 1 := by rw [Finset.card_univ, Fintype.card_fin, h1r]
    omega
  obtain ⟨M, hM⟩ := Formalism.L2.SG.Pf.Cnt.glueExists_holds K F V1 hK hF h1 hsym (nondeg hH) _ hC hP hU0 _ hLat
    hInt hcJ
  exact ⟨M, (glueSet_iff hz0 M).1 hM⟩

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowsMassOfParts

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

end Pos

section Generic

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

end Generic

section Bridge

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_isSymm : (hWb D F0).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [hWb_mk, hWb_mk]
  exact (VS D).herm.eq a.1 b.1

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨Subgroup.one_mem _, fun j => ?_, rfl⟩
  ext x
  simp

theorem one_mem_hz {V1 : Type} [AddCommGroup V1] [Module D.host.E V1]
    (h1 : V1 →ₗ⋆[D.host.E] V1 →ₗ[D.host.E] D.host.E) (z : V1) :
    (1 : V1 ≃ₗ[D.host.E] V1) ∈ hz h1 z :=
  ⟨Subgroup.one_mem _, rfl⟩

theorem gmap_one' {V1 : Type} [AddCommGroup V1] [Module D.host.E V1] [Module (𝓞 D.host.E) V1]
    [IsScalarTower (𝓞 D.host.E) D.host.E V1] (M : Submodule (𝓞 D.host.E) V1) :
    Formalism.HermitianLatticesTheory.gmap (1 : V1 ≃ₗ[D.host.E] V1) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end Bridge

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMass

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem row_lattice_mass : RowsMass := by
  intro D u u' _ F0 what₂ hrows
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  obtain ⟨hd, hk⟩ := anisotropic_complement_definite D u F0
  have hGH : GlueHyp D.host.E D.host.F (hWb D F0) (zbar D F0) (D.mem u).A.T :=
    ⟨hK, hF, hWb_isSymm D F0, hWb_zbar D F0, (D.mem u).A.T_prime.pos, hd⟩
  have hrl : ∀ Λ ∈ what₂, IsRowLat D F0 Λ := hrows.1
  have hinj : Set.InjOn (Mof D F0) (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)) := by
    intro Λ₁ h₁ Λ₂ h₂ he
    obtain ⟨γ, hγ, hγe⟩ := (row_class_holds D u F0 Λ₁ Λ₂ (hrl Λ₁ h₁) (hrl Λ₂ h₂)).2
      ⟨1, one_mem_hz D _ _, by rw [gmap_one' D, he]⟩
    obtain ⟨Λ', _, hu⟩ := hrows.2 Λ₂ (hrl Λ₂ h₂)
    have e1 := hu Λ₁ ⟨h₁, γ, hγ, hγe⟩
    have e2 := hu Λ₂ ⟨h₂, 1, one_mem_stabF D F0, gmap_one' D Λ₂⟩
    rw [e1, e2]
  have hreps : IsHzReps (hWb D F0) (zbar D F0) (what₂.image (Mof D F0)) := by
    refine ⟨fun M hM => ?_, fun M hM => ?_⟩
    · obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hM
      exact row_lattice_mass_holds D u F0 Λ (hrl Λ hΛ)
    · obtain ⟨Λ, hΛ, rfl⟩ := row_surjective D u F0 M hM
      obtain ⟨Λ', ⟨hΛ'm, γ, hγ, hγΛ'⟩, hu⟩ := hrows.2 Λ hΛ
      obtain ⟨σ, hσ, hσM⟩ := (row_class_holds D u F0 Λ' Λ (hrl Λ' hΛ'm) hΛ).1 ⟨γ, hγ, hγΛ'⟩
      refine ⟨Mof D F0 Λ', ⟨Finset.mem_image_of_mem _ hΛ'm, σ, hσ, hσM⟩, ?_⟩
      rintro M'' ⟨hM'', σ', hσ', hσ'M⟩
      obtain ⟨Λ'', hΛ''m, rfl⟩ := Finset.mem_image.1 hM''
      obtain ⟨γ'', hγ'', hγ''Λ⟩ := (row_class_holds D u F0 Λ'' Λ (hrl Λ'' hΛ''m) hΛ).2 ⟨σ', hσ', hσ'M⟩
      rw [hu Λ'' ⟨hΛ''m, γ'', hγ'', hγ''Λ⟩]
  have hk2 : 2 ≤ finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) := by
    rw [hk]
    have := D.R.m_add_three_le_k
    omega
  have hne : ∃ M, IsGlueLat (hWb D F0) (zbar D F0) M :=
    GluedLatticeMass.glued_exists hGH hk2 ⟨Mof D F0 (VS D).L0, RowMPf.Mof_isLattice D F0 _ (VS D).standardTuple_isLattice,
      RowMPf.Mof_unimod D F0 _ (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular⟩
  have e := GluedLatticeMass.glued_lattice_mass_formula hGH (by omega) hne hreps
  rw [hk] at e
  rw [← e, Finset.sum_image hinj]
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_congr rfl fun Λ hΛ => ?_
  unfold wRow
  rw [row_weight_formula D u F0 Λ (hrl Λ hΛ)]

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcLeaves

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcLeaves

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_leaves (a' : ℝ) (ha : 0 < a')
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hχ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAsm.ncTieC_of' X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (Formalism.L2.SG.Pf.NcGlob.normalizing_arithmetic_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha hRR hS hR
      hχ hstd hcong hVo hVt hIx hOm
      (Formalism.L2.SG.Pf.NcVal.diffProd_holds X) PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass hFD hPC hP)

end Formalism.L2.SG.Pf.NcLeaves
end
end
end
