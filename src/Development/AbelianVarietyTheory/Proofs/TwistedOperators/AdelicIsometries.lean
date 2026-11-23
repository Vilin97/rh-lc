module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLOfIsVecBasisAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeetStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProofStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersectionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransportStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  first | exact @GlobalTheory.AdIsomCorrection.correction_of_transport | exact GlobalTheory.AdIsomCorrection.correction_of_transport | (intros; apply GlobalTheory.AdIsomCorrection.correction_of_transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D), IsBasePair X u π L₀ f₀ → ∃ f, IsGlueVec X u L₀ f ∧ ∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f = f₀ w := by
  first | exact @GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | exact GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | (intros; apply GlobalTheory.AdIsom.BaseVec.exists_isGlueVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUniqueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedHermitianLattice_unique : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) (L L' : Submodule (𝓞 D.host.E) Y.V), IsGlued Y X ι z u π L₀ f₀ L → IsGlued Y X ι z u π L₀ f₀ L' → L = L' := by
  first | exact @GlobalTheory.GlueUnique.glued_unique | exact GlobalTheory.GlueUnique.glued_unique | (intros; apply GlobalTheory.GlueUnique.glued_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  first | exact @GlobalTheory.HypLattice.isSelfDualC_lamN | exact GlobalTheory.HypLattice.isSelfDualC_lamN | (intros; apply GlobalTheory.HypLattice.isSelfDualC_lamN <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOverStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localLattice_eq_iff_idempotent_components_over : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  first | exact @GlobalTheory.LocHat.locL_eq_iff_idem | exact GlobalTheory.LocHat.locL_eq_iff_idem | (intros; apply GlobalTheory.LocHat.locL_eq_iff_idem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDualLattice_image_adelicUnitary : ∀ D : D7, ImageSt D := by
  first | exact @GlobalTheory.AdIsomImage.imageSt | exact GlobalTheory.AdIsomImage.imageSt | (intros; apply GlobalTheory.AdIsomImage.imageSt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometries

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem transportSt (D : D7) : TransportSt D := by
  intro W Y hr L Λ hL hΛ S hS n be be' h h'
  refine ⟨exists_transport W Y hr L Λ hL hΛ S hS n be be' h h', fun x hx x' => ?_⟩
  first
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' (selfDual_isFullLattice hL) h x hx x'
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' hL.1 h x hx x'

private theorem fullLattice_of_glueVec {X : HSp D} {u : D.what₂.Word} {L₀ : Lat X}
    {f : Fin X.rank → EAf D} (hL : L₀.FG) (hf : IsGlueVec X u L₀ f) :
    Submodule.IsFullLattice D.host.E L₀ := by
  let β₀ : GL (Fin X.rank) (EAf D) := 1
  have hstd := GlobalTheory.NormSum.AdLattice.lat_isLattice β₀
  have hfull : Submodule.IsFullLattice D.host.E (L₀ ⊔ lat β₀) :=
    Submodule.IsFullLattice.of_le_of_fg _ le_sup_right (hL.sup hstd.fg)
  obtain ⟨β, hβ⟩ := exists_eq_lat hfull
  obtain ⟨β', hβ', -⟩ := exists_dual_frame X β
  have hle : L₀ ≤ lat β := hβ ▸ le_sup_left
  have := GlobalTheory.NormSum.AdLattice.lat_isLattice β'
  have := Submodule.IsLattice.of_fg D.host.E hL
  let t : D.host.Eˣ := Units.mk0 (Tu D u) (Tu_ne_zero u)
  refine Submodule.IsFullLattice.of_le D.host.E (M := t • lat β') ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  apply GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL
  let xA : Fin X.rank → EAf D := fun i => inc D (x i)
  have hxA : ∀ z ∈ hat L₀, hA X z xA ∈ OA D :=
    fun z hz => (dual_hat_lat hβ' xA).2 (inc_mem_hat hx) z (hat_mono hle hz)
  obtain ⟨a, ha, hxa⟩ := hf.dual xA hxA
  have htx := add_mem_hat (smul_mem_hat (inc_Tu_mem u) hxa) (smul_mem_hat ha hf.mul_mem)
  rw [smul_sub, smul_comm (inc D (Tu D u)) a, sub_add_cancel] at htx
  convert htx using 1
  funext i
  change inc D (Tu D u * x i) = inc D (Tu D u) * inc D (x i)
  exact map_mul _ _ _

theorem gluedSt (D : D7) : GluedSt D := by
  intro u π hπ Y X ι z hz L₀ f₀ hb
  obtain ⟨f, hf, hff⟩ := GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData D u π hπ X L₀ f₀ hb
  have hL₀ := fullLattice_of_glueVec hb.1.fg hf
  obtain ⟨x, hx⟩ := exists_sub_inc_mem_hat (D := D) (Λ := L₀) hL₀.span_eq_top f
  obtain ⟨x₀, hx₀⟩ := vA_surj X x
  rw [← hx₀] at hx
  have hg : IsGlueVec X u L₀ (vA X x₀) := hf.congr hx
  have hgl : IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
    refine GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz L₀ x₀ f₀ hL₀.toIsLattice hg (fun w hw => ⟨?_, ?_⟩)
    · rw [← hff w hw, smul_smul, idem_mul_self]
    · rw [← hff w hw, ← smul_sub]
      exact smul_mem_hat (idem_mem w) hx
  have huniq : ∀ L, IsGlued Y X ι z u π L₀ f₀ L → L = glueLat Y X ι z u L₀ x₀ :=
    fun L hL => GlobalTheory.T.gluedHermitianLattice_unique D u π hπ Y X ι z L₀ f₀ L _ hL hgl
  refine ⟨⟨_, hgl, huniq⟩, fun L hL => ?_⟩
  rw [huniq L hL]
  exact GlobalTheory.T.gluedLattice_selfDual_primitive_meet D u Y X ι z hz L₀ x₀ hL₀ hg

theorem ungluedSt (D : D7) : UngluedSt D := by
  intro u π hπ Y X ι z hz L hSD hP
  obtain ⟨hlat, x₀, hL⟩ := GlobalTheory.T.primitive_lattice_glued_from_intersection D u Y X ι z hz L hSD hP

  have hg : IsGlueVec X u (capX Y X ι L) (vA X x₀) := by
    have key := GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive D u Y X ι z hz (capX Y X ι L) x₀ hlat
    rw [← hL] at key
    exact key hSD hP
  have := hlat
  refine ⟨fun w => idem w • vA X x₀,
    GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector D u π hπ X _ _ (by infer_instance) hg, ?_⟩
  have key := GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz (capX Y X ι L) x₀ (fun w => idem w • vA X x₀) hlat.toIsLattice hg
    (fun w _ => ⟨by simp only [smul_smul, idem_mul_self], by simp only [sub_self]; exact zero_mem_hat⟩)
  rwa [← hL] at key

theorem adelicIsometries (D : D7) : AdelicIsometries D := by
  unfold AdelicIsometries LamNSt
  exact ⟨plIdemSt D, transportSt D, GlobalTheory.T.correctionSt_of_transportSt D (transportSt D),
    splitGlueSt_of D (fun n Λ Λ' hΛ hΛ' v => GlobalTheory.T.localLattice_eq_iff_idempotent_components_over D n Λ Λ' hΛ hΛ' v),
    GlobalTheory.T.selfDualLattice_image_adelicUnitary D, GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D, GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry D (GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D), GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof D,
    gluedSt D, ungluedSt D,
    ⟨fun u Y X ι z ρ e f h L hL nn hn => GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable D u Y X ι z ρ e f h L hL nn hn,
      (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).1, (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).2⟩,
    frameSt D⟩

end GlobalTheory.AdIsom

end
end
end
