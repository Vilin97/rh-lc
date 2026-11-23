module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoprimeProjectionAdelicLatticeIntoColumnsStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsSpanAdelicLatticeModLevelStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosen

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameFull

variable {D : D7}

theorem mL_div (I : Formalism.MainNotions.S.AutInst) (m : ℕ) :
    ∀ v ∈ mL I m, ∃ z ∈ I.Lf, v = (m : I.E ⊗[I.F] Af I.F) • z := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, I.Lf.zero_mem, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, I.Lf.add_mem ha hb, (smul_add _ _ _).symm⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, I.Lf.smul_mem c ha, smul_comm _ _ _⟩

theorem embA_smul (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
  simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem embA_zero (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA 0 = 0 := by
  simp [embA]

theorem step (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hmem : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)
    (m : ℕ) (w : VA X.B.I) (hw : w ∈ X.B.I.Lf)
    (hwe : embA X wt ιA (c • y) = (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) :
    ∃ z ∈ hat D.host.F (Mq wt), c • y = (m : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero]
    apply hinj
    rw [hwe, embA_zero, Nat.cast_zero, zero_smul]
  · have hF : IsUnit ((m : D.host.F)) := (Nat.cast_ne_zero.mpr hm.ne').isUnit
    have hR : IsUnit ((m : D.host.E ⊗[D.host.F] Ad D.host.F)) := by
      simpa using hF.map (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))
    obtain ⟨t, ht⟩ := hR.exists_right_inv
    refine ⟨t • (c • y), ?_, ?_⟩
    · rw [hmem, embA_smul, hwe, smul_smul, ← map_natCast ιA.symm m, ← map_mul, mul_comm, ht, map_one, one_smul]
      exact hw
    · rw [smul_smul, ht, one_smul]

theorem symm_unit (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA) :
    ιA.symm (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) =
      1 - X.ew - sigA X.B.I X.ew := by
  have h := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI X.ew
  apply ιA.injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_sub, map_one]
  exact congrArg (fun t => 1 - ιA X.ew - t) h.symm

theorem emb_mem (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA)
    (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (hy : embA X wt ιA y ∈ X.B.I.Lf) :
    ∃ w ∈ X.B.I.Lf, embA X wt ιA
      ((1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y) =
      ((D.host.g 0 * D.host.g 1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
  rw [embA_smul, symm_unit X ιA hI]
  obtain ⟨w, hw, hw'⟩ := mL_div X.B.I X.B.g _ (X.ew_full _ hy)
  exact ⟨w, hw, by rw [hw', X.g_eq]⟩

theorem eps_full : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  intro D X u wt ιA hW hI y hy
  obtain ⟨hmem, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨w, hw, hwe⟩ := emb_mem X wt ιA hI y ((hmem y).1 hy)
  exact step X wt ιA hmem hinj _ y _ w hw hwe

end GlobalTheory.St.G.FrameFull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosenStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  first | exact @GlobalTheory.St.G.FrameFull.eps_full | exact GlobalTheory.St.G.FrameFull.eps_full | (intros; apply GlobalTheory.St.G.FrameFull.eps_full <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevelStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.projection_moves_typeVectors_modLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), (∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.St.G.FrameClose.typeVec_close | exact GlobalTheory.St.G.FrameClose.typeVec_close | (intros; apply GlobalTheory.St.G.FrameClose.typeVec_close <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTraceStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.St.G.psiEf_transport_rat | exact GlobalTheory.St.G.psiEf_transport_rat | (intros; apply GlobalTheory.St.G.psiEf_transport_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempot

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameEps

theorem beps : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  intro D X u wt ιA hW hA c p b bd hb hbd
  have hinj := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).2.2.1
  have semi : ∀ a x, embA X wt ιA (ιA a • x) = a • embA X wt ιA x := by
    intro a x
    simp only [embA, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul,
      RingEquiv.symm_apply_apply, mul_smul]
  constructor
  · intro i
    apply hinj
    rw [semi, hb, smul_comm X.ew, ← map_smul p X.ew, ← Matrix.mulVec_smul _ X.ew, ← X.bw_w i]
  · intro i
    apply hinj
    have hs : Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) = ιA (sigA X.B.I X.ew) :=
      (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA X.ew).symm
    rw [hs, semi, hbd, smul_comm (sigA X.B.I X.ew), ← map_smul p (sigA X.B.I X.ew),
      ← Matrix.mulVec_smul _ (sigA X.B.I X.ew), ← X.bwd_w i]

end GlobalTheory.St.G.FrameEps
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempotStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  first | exact @GlobalTheory.St.G.FrameEps.beps | exact GlobalTheory.St.G.FrameEps.beps | (intros; apply GlobalTheory.St.G.FrameEps.beps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReference

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameLink

theorem frame_exists : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  intro D X u wt ιA hW hI
  obtain ⟨c, p, hc, hrng, hid, hLf, hkill, hkz, hcl⟩ := GlobalTheory.T.exists_coprime_projection_adelic_lattice_into_columns D X u wt ιA hW hI
  have hmhat := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf ∧ X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf := fun i =>
    ⟨(X.xu_K u (X.bw i)).1 (X.vectorsInLattice.2.2 i).1, (X.xu_K u (X.bwd i)).1 (X.vectorsInLattice.2.2 i).2⟩
  have hb0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bw i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  have hbd0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  choose b hb using hb0
  choose bd hbd using hbd0
  have hclose := GlobalTheory.T.projection_moves_typeVectors_modLevel D X u wt ιA hW hI c p hcl
  have hbe := GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent D X u wt ιA hW hI c p b bd hb hbd
  refine ⟨{ eps := ιA X.ew
            eps_idem := by rw [← map_mul, X.ew_idem]
            eps_orth := by rw [← GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI, ← map_mul, X.ew_orth, map_zero]
            eps_int := (hI.2 _).1 X.ew_int
            eps_full := GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen D X u wt ιA hW hI
            b := b
            bd := bd
            b_mem := fun i => (hmhat.1 (b i)).2 (by rw [hb i]; exact hLf _ (hY i).1)
            bd_mem := fun i => (hmhat.1 (bd i)).2 (by rw [hbd i]; exact hLf _ (hY i).2)
            b_eps := hbe.1
            bd_eps := hbe.2
            dual := GlobalTheory.T.transported_type_vectors_dual_mod_level D X u wt ιA hW hI c p b bd hb hbd hclose
            span := GlobalTheory.T.transportedTypeVectors_span_adelicLattice_modLevel D X u wt ιA hW hI c p hc hid hLf hkill hkz b bd hb hbd
            psi := fun a => X.psiEf (ιA.symm a)
            psi_add := fun x y => by
              show X.psiEf (ιA.symm (x + y)) = X.psiEf (ιA.symm x) * X.psiEf (ιA.symm y)
              rw [RingEquiv.map_add (e := _), X.psiEf_add]
            psi_int := fun x hx => X.psiEf_int _ ((hI.2 _).2 (by simpa using hx))
            psi_rat := GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace D X ιA hI }, rfl, fun i => ?_, fun i => ?_, fun a => rfl⟩
  · show embA X wt ιA (b i) - _ ∈ _
    rw [hb i]; exact (hclose i).1
  · show embA X wt ιA (bd i) - _ ∈ _
    rw [hbd i]; exact (hclose i).2

end GlobalTheory.St.G.FrameLink
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReferenceStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frame_adelicColumnLattice_linked_reference : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  first | exact @GlobalTheory.St.G.FrameLink.frame_exists | exact GlobalTheory.St.G.FrameLink.frame_exists | (intros; apply GlobalTheory.St.G.FrameLink.frame_exists <;> assumption)
end
end
