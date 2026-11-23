module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVectorStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModuleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumEqSumOrbitReps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPart

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem lat0_eq_img_latIn_Ub (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W)
    (he : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ
      = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  ext w
  rw [GlobalTheory.Mass.Transp.mem_img]
  have hd : ((e (e.symm w) : W) : (VS D).V) - (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
      ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X :=
    (le_sup_right : GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ≤ _) (he (e.symm w))
  rw [LinearEquiv.apply_symm_apply] at hd
  have h1 : w ∈ GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ ↔
      (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  have h2 : e.symm w ∈ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ↔
      (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
        ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  rw [h1, h2]
  constructor
  · intro h
    simpa using Submodule.sub_mem _ h hd
  · intro h
    simpa using Submodule.add_mem _ hd h

end GlobalTheory.RowsOrb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPartStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W), (∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X) → ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | exact GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | (intros; apply GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.StabSet

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowMean

theorem main : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  intro D X u M₀ ψ hψ
  have hU : ∀ v, v ∈ GlobalTheory.RowsOrb.Ub X u ↔ GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) v = 0 :=
    fun v => GlobalTheory.RowsOrb.mem_Ub X u v
  have hπ : ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)),
      GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) =
        resZ (GlobalTheory.RowsOrb.hb X) hU g • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L :=
    fun g L => StabSplit.latIn_smul (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Ub X u) g.1 (smul_compl _ hU g) L
  have hY : Stable (isom (GlobalTheory.RowsOrb.hU X u)) (genus (GlobalTheory.RowsOrb.hU X u) M₀) :=
    Transp.genus_stable (R := 𝓞 D.host.E) (K := D.host.E) (V := GlobalTheory.RowsOrb.Ub X u) (h := GlobalTheory.RowsOrb.hU X u) M₀
  refine ⟨?_, fun g L => by rw [hπ]; exact hψ _ _⟩
  rintro g L ⟨h1, h2, h3, h4⟩
  have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 D.host.E) D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) g.1.1 g.1.2 L
  refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, ?_⟩
  · have hg : g.1.1 (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    have hs : g.1.1.symm (t • GlobalTheory.RowsOrb.zb X u) = t • GlobalTheory.RowsOrb.zb X u :=
      g.1.1.symm_apply_eq.2 (by rw [map_smul, hg])
    change t • GlobalTheory.RowsOrb.zb X u ∈ Formalism.HermitianLatticesTheory.gmap (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) L ↔ _
    rw [isomAct_mem_gmap, hs, h3]
  · let s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u) := resZ (GlobalTheory.RowsOrb.hb X) hU g
    have k : s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀ := hY s _ h4
    have e : GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) = s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L := hπ g L
    exact Eq.mpr (congrArg (fun N => N ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀) e) k

end GlobalTheory.RowsOrb.StabSet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizerStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  first | exact @GlobalTheory.RowsOrb.StabSet.main | exact GlobalTheory.RowsOrb.StabSet.main | (intros; apply GlobalTheory.RowsOrb.StabSet.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitiveStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.orbit_lattice_unimodular_and_primitive : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Submodule.IsLattice D.host.E (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ ∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ GlobalTheory.RowsOrb.Lmap X u Λ ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  first | exact @GlobalTheory.RowsOrb.Basic.lmap_basic | exact GlobalTheory.RowsOrb.Basic.lmap_basic | (intros; apply GlobalTheory.RowsOrb.Basic.lmap_basic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLatticesStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ₁ ∈ Y.what₂ u, ∀ Λ₂ ∈ Y.what₂ u, ∀ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ₁ = GlobalTheory.RowsOrb.Lmap X u Λ₂ → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.RowsOrb.rows_eq_of_conj | exact GlobalTheory.RowsOrb.rows_eq_of_conj | (intros; apply GlobalTheory.RowsOrb.rows_eq_of_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem cardE (α : Type) [Nonempty α] :
    ENNReal.ofReal ((Nat.card α : ℝ)⁻¹) = ((ENat.card α : ℕ∞) : ℝ≥0∞)⁻¹ := by
  rcases finite_or_infinite α with h | h
  · have h0 : 0 < Nat.card α := Nat.card_pos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]
    simp
  · rw [Nat.card_eq_zero_of_infinite, ENat.card_eq_top_of_infinite]
    simp


theorem rowsOrbC : GlobalTheory.TypeAsm.RowsOrbC := by
  intro D large₂ X Y u hS W HW hEmb φ hφ Λ₀ hΛ₀
  obtain ⟨e, he, heX⟩ := GlobalTheory.T.anisotropicOrthogonal_isometric_definiteModel D X u W HW hEmb
  have hlat := GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart D X u W e heX
  set M₀ := GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ₀) with hM₀
  obtain ⟨hψ, hgen, horb⟩ := GlobalTheory.T.isometry_transports_genus_orbitSum D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he φ hφ M₀
  obtain ⟨hcm, -, -, -, hf, -, -, -, -, -, -, -, hTu⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨hTp, hsp⟩ := hTu u
  have hl0 := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hS W HW hEmb Λ₀ hΛ₀
  rw [hlat Λ₀] at hl0
  obtain ⟨hM₀i, hM₀d⟩ := GlobalTheory.T.isometry_transports_discriminantModule D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he M₀ _ hl0.1 hl0.2
  have hbs : (GlobalTheory.RowsOrb.hb X).IsSymm := ⟨fun a b => (VS D).herm.eq (a : (VS D).V) (b : (VS D).V)⟩
  have hz : GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.zb X u) = -((Tu D u : ℕ) : D.host.E) := X.zu_norm u
  have hrm := GlobalTheory.Mass.RowMean.main D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) hcm hbs (Tu D u)
    (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.Ub X u) hTp hsp hz rfl (GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite D X u) M₀ hM₀i hM₀d
    (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  simp only [hlat, ← hM₀, hgen]
  rw [horb, ← hf]
  refine Eq.trans ?_ hrm
  obtain ⟨hst, hinv⟩ := GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer D X u M₀ (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  have hinj : ∀ a ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      ∀ b ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      GlobalTheory.RowsOrb.Lmap X u a = GlobalTheory.RowsOrb.Lmap X u b → a = b := by
    intro a ha b hb hab
    exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 1 ((one_smul (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u a)).trans hab)
  refine Eq.trans ?_ (GlobalTheory.Mass.orbSum_eq_sum_reps (GlobalTheory.RowsOrb.Gz X u) (Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X))
    {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} (fun L => φ (GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L))) hst (fun g L => hinv g L)
    (((Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀)).image (GlobalTheory.RowsOrb.Lmap X u)) ?_ ?_).symm
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    congr 1
    show ENNReal.ofReal ((Nat.card (autLz D (X.Fu u) Λ) : ℝ)⁻¹) = _
    rw [GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer D large₂ X Y u hS Λ (Finset.mem_filter.1 hΛ).1, cardE]
  · intro L hL
    obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hΛr, hΛg⟩ := Finset.mem_filter.1 hΛ
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.orbit_lattice_unimodular_and_primitive D large₂ X Y u hS Λ hΛr
    exact ⟨h1, h2, h3, hΛg⟩
  · intro L hL
    obtain ⟨Λ, hΛ, g, hg⟩ := GlobalTheory.T.exists_row_of_unimodular_lattice_primitive_vector D large₂ X Y u hS L hL.1 hL.2.1 hL.2.2.1
    refine ⟨GlobalTheory.RowsOrb.Lmap X u Λ, ⟨Finset.mem_image.2 ⟨Λ, Finset.mem_filter.2 ⟨hΛ, ?_⟩, rfl⟩, g, hg⟩, ?_⟩
    · have := hst g⁻¹ L hL
      erw [← hg, inv_smul_smul] at this
      exact this.2.2.2
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.1 hy
      congr 1
      exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS Λ' (Finset.mem_filter.1 hΛ').1 Λ hΛ (g⁻¹ * g') (by erw [mul_smul, hg', ← hg, inv_smul_smul])

end GlobalTheory.RowsOrb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparisonStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.rowsGenus_weightedSumComparison : GlobalTheory.TypeAsm.RowsOrbC := by
  first | exact @GlobalTheory.RowsOrb.rowsOrbC | exact GlobalTheory.RowsOrb.rowsOrbC | (intros; apply GlobalTheory.RowsOrb.rowsOrbC <;> assumption)
end
end
