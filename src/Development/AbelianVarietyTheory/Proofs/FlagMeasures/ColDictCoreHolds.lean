module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatchStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormsOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
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
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroFormsStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnDictionary_into_stepZeroForms : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  first | exact @GlobalTheory.St.colDictInto_of_levelMatch | exact GlobalTheory.St.colDictInto_of_levelMatch | (intros; apply GlobalTheory.St.colDictInto_of_levelMatch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumInnerClassRepsIndep

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentatives

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colDict_isometric_of_reps :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  intro D X u F Tr hK hsig hL hS what₂ cs hinj hreps T T'
  obtain ⟨hcls, hwt⟩ := GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hsig hL
  have hwt1 := hwt hS
  obtain ⟨hψ, hπ, heq, -, -⟩ := GlobalTheory.St.cols_sharp_dictionary D X u hK
  have key := GlobalTheory.sum_inner_classReps_indep (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u)
    (Ku X u hK) (psiK X u hK) (X.Vpi u) (piRep X u) hπ hψ cs.Cl ((D.mem u).C.cls 0) cs.h Tr.hc hreps hcls
    (shP X u (toCu X hK T').1) (shP X u (toCu X hK T).1) (heq _) (heq _)
  have hsh : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) ρ, (Formalism.L2.SG.PackageTie2.shT hinj S).ofLp ρ = shP X u (toCu X hK S).1 (cs.h ρ) := fun S ρ => rfl
  show inner ℂ (Formalism.L2.SG.PackageTie2.shT hinj T') (Formalism.L2.SG.PackageTie2.shT hinj T) = _
  rw [PiLp.inner_apply]
  simp only [hsh]
  rw [key]
  have hd : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) c, colDictL X Tr hK (toCu X hK S) c = fun z => Tr.J (shP X u (toCu X hK S).1 (Tr.hc c)) (F.val0.eY z) := fun S c => rfl
  have hterm : ∀ c, (D.fm u).ipV 0 c (colDictL X Tr hK (toCu X hK T) c) (colDictL X Tr hK (toCu X hK T') c) = ⟪shP X u (toCu X hK T').1 (Tr.hc c), shP X u (toCu X hK T).1 (Tr.hc c)⟫_ℂ := by
    intro c
    rw [hd, hd]
    exact Tr.J_isom c _ _
  unfold Formalism.BasicNotions.MemberForms.ipC
  simp only [hwt1, one_mul, hterm]

end GlobalTheory.St

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentativesStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnDictionary_isometric_of_representatives : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  first | exact @GlobalTheory.St.colDict_isometric_of_reps | exact GlobalTheory.St.colDict_isometric_of_reps | (intros; apply GlobalTheory.St.colDict_isometric_of_reps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hConj hLev).1, GlobalTheory.T.columnDictionary_into_stepZeroForms D X u F Tr hK hConj hLev,
    GlobalTheory.T.columnDictionary_bijective_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact GlobalTheory.T.columnDictionary_isometric_of_representatives D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
end
end
