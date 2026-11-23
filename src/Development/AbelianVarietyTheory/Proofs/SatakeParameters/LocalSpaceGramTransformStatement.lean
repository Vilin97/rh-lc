module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.LatDet

theorem det_isUnit_of_colSpan {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
    (hinj : Function.Injective (algebraMap W Qq)) {N : ℕ} (M : Matrix (Fin N) (Fin N) Qq)
    (h1 : ∀ i c, M i c ∈ (algebraMap W Qq).range) (h2 : ∀ i, Pi.single i (1 : Qq) ∈ colSpan W M) :
    ∃ y : Wˣ, M.det = algebraMap W Qq y := by
  choose M0' hM0 using h1
  let M0 : Matrix (Fin N) (Fin N) W := fun i c => M0' i c
  have hM : M = M0.map (algebraMap W Qq) := by
    ext i c; rw [Matrix.map_apply]; exact (hM0 i c).symm
  have h2' : ∀ i, ∃ c : Fin N → W, ∑ k, c k • (fun r => M r k) = Pi.single i (1 : Qq) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun W).1 (h2 i)
  choose C hC using h2'
  let C0 : Matrix (Fin N) (Fin N) W := fun k i => C i k
  have hMC : M * C0.map (algebraMap W Qq) = 1 := by
    ext r i
    have := congrFun (hC i) r
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    simp only [Algebra.smul_def] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h3 : ∑ k, M r k * (C0.map (algebraMap W Qq)) k i = ∑ k, algebraMap W Qq (C i k) * M r k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, mul_comm]
    rw [h3, this, Pi.single_apply]
  have h4 : (M0 * C0).map (algebraMap W Qq) = (1 : Matrix (Fin N) (Fin N) W).map (algebraMap W Qq) := by
    rw [Matrix.map_mul, ← hM, hMC, Matrix.map_one _ (map_zero _) (map_one _)]
  have h5 : M0 * C0 = 1 := by
    ext i c
    have := congrFun (congrFun h4 i) c
    exact hinj (by simpa using this)
  have h6 : M0.det * C0.det = 1 := by rw [← Matrix.det_mul, h5, Matrix.det_one]
  refine ⟨⟨M0.det, C0.det, h6, by rw [mul_comm, h6]⟩, ?_⟩
  show M.det = algebraMap W Qq M0.det
  rw [hM]
  exact (RingHom.map_det (algebraMap W Qq) M0).symm

theorem rho_int_mem {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) (x : 𝓞 E) : ρ x ∈ (algebraMap W Qq).range := by
  have hx : IsIntegral ℤ (x : E) := NumberField.RingOfIntegers.isIntegral_coe x
  have h1 : IsIntegral ℤ (ρ x) := hx.map ρ.toIntAlgHom
  have h2 : IsIntegral W (ρ x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨y, hy⟩

theorem mulVec_mem_locSp_mvL {E W Qq : Type} [Field E] [NumberField E] [StarRing E] [CommRing W] [Field Qq] [Algebra W Qq]
    (ρ : E →+* Qq) {N : ℕ} (g : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ L) : (g.1.map ρ) *ᵥ z ∈ locSp W ρ (mvL g L) := by
  let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((g.1.map ρ).mulVecLin).restrictScalars W
  have hle : locSp W ρ L ≤ (locSp W ρ (mvL g L)).comap f := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    change (g.1.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ (mvL g L)
    have h1 : (g.1.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((g.1 *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ g.1 x k).symm
    rw [h1]
    refine Submodule.subset_span ⟨g.1 *ᵥ x, ?_, rfl⟩
    exact Submodule.mem_map.2 ⟨x, hx, by simp [toLE_apply]⟩
  exact hle hz

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem locSp_std_int {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) {N : ℕ} {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))) (i : Fin N) :
    z i ∈ (algebraMap W Qq).range := by
  let P : Submodule W (Fin N → Qq) := Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap W Qq))
  have hle : locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E))) ≤ P := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩ k -
    have hk : x k ∈ (1 : Submodule (𝓞 E) E) := hx k trivial
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hk
    obtain ⟨w', hw⟩ := rho_int_mem (W := W) ρ y
    refine ⟨w', ?_⟩
    rw [Algebra.linearMap_apply, hw]
    show ρ ↑y = ρ (x k)
    rw [← hy]
  obtain ⟨w', hw⟩ := hle hz i trivial
  exact ⟨w', hw⟩

theorem det_unit_of_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] (ρ : E →+* Qq) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : IsUnit (T : W))
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb) (crd B : GL (Fin N) E)
    (hbase : mvL crd (compan (sp := sp) J a Lb) = Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))
    (hB : locSp W ρ Lb = colSpan W (B.1.map ρ)) :
    ∃ y : Wˣ, ρ (crd.1.det * B.1.det) = algebraMap W Qq y := by
  have hc := CompSp.locSp_compan_eq sp W Qq ρ J a T Lb hT hdual
  rw [hB] at hc
  let M : Matrix (Fin N) (Fin N) Qq := crd.1.map ρ * B.1.map ρ
  have hdet : ρ (crd.1.det * B.1.det) = M.det := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, Matrix.det_mul]
    rfl
  rw [hdet]
  have hcolM : ∀ c, (crd.1.map ρ) *ᵥ (fun r => (B.1.map ρ) r c) = fun r => M r c := fun c => by
    funext r
    rfl
  apply det_isUnit_of_colSpan (IsFractionRing.injective W Qq) M
  · intro i c
    have hcol : (fun r => (B.1.map ρ) r c) ∈ colSpan W (B.1.map ρ) := Submodule.subset_span ⟨c, rfl⟩
    rw [← hc] at hcol
    have h1 := mulVec_mem_locSp_mvL ρ crd _ hcol
    rw [hbase, hcolM] at h1
    exact locSp_std_int ρ h1 i
  · intro i
    have hei : Pi.single i (1 : E) ∈ Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)) := by
      intro k _
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    rw [← hbase] at hei
    obtain ⟨x, hx, hx'⟩ := Submodule.mem_map.1 hei
    have hx2 : crd.1 *ᵥ x = Pi.single i (1 : E) := by
      rw [← hx']
      simp [toLE_apply]
    have hρx : (fun k => ρ (x k)) ∈ colSpan W (B.1.map ρ) := hc ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun W).1 hρx
    unfold colSpan
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨cc, ?_⟩
    let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((crd.1.map ρ).mulVecLin).restrictScalars W
    have hf : ∀ c, f (fun r => (B.1.map ρ) r c) = fun r => M r c := hcolM
    have h3 : f (fun k => ρ (x k)) = Pi.single i (1 : Qq) := by
      show (crd.1.map ρ) *ᵥ (fun k => ρ (x k)) = _
      funext r
      have h4 := RingHom.map_mulVec ρ crd.1 x r
      rw [hx2] at h4
      rw [show (fun k => ρ (x k)) = ⇑ρ ∘ x from rfl, ← h4, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp

    rw [← h3, ← hcc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hf]

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem latAd_one_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    latAd (1 : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb := by
  apply le_antisymm
  · rw [latAd, Submodule.span_le]
    intro x hx
    apply Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Lb hfin x
    simp only [Set.mem_setOf_eq, inv_one, Units.val_one, Matrix.one_mulVec] at hx
    exact hx
  · intro x hx
    apply Submodule.subset_span
    show _ ∈ {x | _}
    simp only [Set.mem_setOf_eq, inv_one, Units.val_one, Matrix.one_mulVec]
    exact (Submodule.subset_span ⟨x, hx, rfl⟩ : (fun i => inclE (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)

theorem crd_mul_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β B v hB
  have hbase := J.base j hj β
  unfold latCo at hbase
  rw [latAd_one_eq _ ((J.St j hj).K β).lev.Lb_fin] at hbase
  have hTe := J.tie.T_eq j hj
  have hdual := ((J.St j hj).K β).lev.Lb_dual
  have hset := ((sysS H X std).G.P.setting v)
  haveI := hset.frac_alt
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2)
  have hTu : IsUnit (((D.mem u).A.T : ℕ) : (sysS H X std).G.P.W v) := natCast_isUnit_localRing (sysS H X std) v _ hcop
  rw [← hTe] at hTu
  exact det_unit_of_base D.sp (J.rho std v) (gramN D j hj) J.a (J.St j hj).T _ hTu hdual (J.A.crd j hj) B hbase hB

end GlobalTheory.TwV.LatDet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.LatDet.crd_mul_det_unit | exact GlobalTheory.TwV.LatDet.crd_mul_det_unit | (intros; apply GlobalTheory.TwV.LatDet.crd_mul_det_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.UnitPos

theorem norm_twG_le {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.W v) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y)‖ ≤ 1 := by
  have h := E.compat v s.val y
  have e : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y) =
      E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) y))) := rfl
  rw [e, h, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

theorem norm_twG_unit {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : (X.G.P.W v)ˣ) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_le X E v s (y : X.G.P.W v)
  have h2 := norm_twG_le X E v s ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have hm : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v)) *
      twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hn := congrArg norm hm
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ := norm_nonneg _
  have h0' : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))‖ := norm_nonneg _
  nlinarith

end GlobalTheory.TwV.UnitPos

namespace GlobalTheory.TwV.UnitPos

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom

end GlobalTheory.TwV.UnitPos


open GlobalTheory.TwV.UnitPos in
theorem GlobalTheory.TwV.UnitPos.norm_embT_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι b hb hloc τ
  obtain ⟨⟨v, s⟩, rfl⟩ := (hT.gat_pos u w hg).surjective τ
  have hq := embT_mem_qbar D ((hT.gat_pos u w hg) ⟨v, s⟩) b
  have e1 : ι (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) := by
    rw [TaylorLogMetric.lamC, dite_eq_left hq]
    exact hι ⟨_, hq⟩
  rw [e1, hS v s b]
  obtain ⟨y, hy⟩ := hloc v
  split_ifs with ho
  · have hc : J.rho std v (D.host.conj b) = algebraMap _ _ (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) := by
      have h1 : J.rho std v (D.host.conj b) * J.rho std v b = 1 := by
        rw [← map_mul, mul_comm, hb, map_one]
      have h2 : algebraMap ((sysS H X std).G.P.W v) ((sysS H X std).G.P.Qq v) (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) *
          J.rho std v b = 1 := by
        rw [hy, ← map_mul, Units.inv_mul, map_one]
      have hne : J.rho std v b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    rw [hc]
    exact norm_twG_unit _ S.E v s _
  · rw [hy]
    exact norm_twG_unit _ S.E v s y
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  first | exact @GlobalTheory.TwV.UnitPos.norm_embT_unit | exact GlobalTheory.TwV.UnitPos.norm_embT_unit | (intros; apply GlobalTheory.TwV.UnitPos.norm_embT_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.DelB.UnitB

theorem det_map_transpose {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    ((M.map σ)ᵀ).det = σ M.det := by
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_unitary_prod {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (J c B : Matrix (Fin N) (Fin N) E)
    (hc : (c.map σ)ᵀ * c = J) (hB : (B.map σ)ᵀ * J * B = 1) :
    σ (c.det * B.det) * (c.det * B.det) = 1 := by
  have h : ((c * B).map σ)ᵀ * (c * B) = 1 := by
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (B.map σ)ᵀ * (c.map σ)ᵀ * (c * B) = (B.map σ)ᵀ * ((c.map σ)ᵀ * c) * B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hB]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, det_map_transpose, Matrix.det_one, Matrix.det_mul] at hd
  exact hd

end GlobalTheory.TwV.DelB.UnitB


open GlobalTheory.TwV.DelB.UnitB in
theorem GlobalTheory.TwV.DelB.detCrdB_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj β B hB hL τ
  refine GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one S hPos ι hι _ ?_ (fun v => GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit S j hj β B v (hL v)) τ
  have hc := J.pins.crd_orth j hj
  have h1 := det_unitary_prod (sigD D : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj).1 B.1 hc hB
  have hconj : ∀ y : D.host.E, D.host.conj y = (sigD D : D.host.E →+* D.host.E) y := fun y => (bridge_star_holds D.R D.host y).symm
  rw [hconj, mul_comm]
  exact h1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_space_gram_transform : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelB.detCrdB_unit | exact GlobalTheory.TwV.DelB.detCrdB_unit | (intros; apply GlobalTheory.TwV.DelB.detCrdB_unit <;> assumption)
end
end
