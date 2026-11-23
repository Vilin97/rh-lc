module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIdealAtT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
import Mathlib.Tactic.Linter.Style
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineUnit

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped NNReal

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {k : ℕ}

theorem exists_lt_nnnorm (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : ∃ t : Fv F v, C < ‖t‖₊ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm (Fv F v) (C : ℝ)
  exact ⟨t, by exact_mod_cast ht⟩

theorem valBar_smul (τ : E →ₐ[F] FvBar F v) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    valBar F v (finEmb F v τ (t • y)) = ‖t‖₊ * valBar F v (finEmb F v τ y) := by
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  exact absBar_algebraMap F v t

theorem mem_intLoc_iff_valBar {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ ∀ τ : E →ₐ[F] FvBar F v, valBar F v (finEmb F v τ y) ≤ 1 :=
  mem_intLoc_iff_absFin_le_one.trans (absFin_le_iff F v)

theorem exists_valBar_ne_zero {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) (τ : E →ₐ[F] FvBar F v) :
    ∃ j, valBar F v (finEmb F v τ (u j)) ≠ 0 := by
  by_contra hc
  push Not at hc
  have := congrArg (finEmb F v τ) h

  rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by
  rw [map_mul, (Valuation.zero_iff _).1 (hc j), mul_zero]] at this
  exact zero_ne_one this

theorem mem_intLoc_of_stable {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, a * u j ∈ intLoc F E v) → ∀ j, c * a * u j ∈ intLoc F E v) : c ∈ intLoc F E v := by
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (Finset.univ.sup fun j => absFin F v (u j))
  have ht0 : ‖t‖₊ ≠ 0 := (lt_of_le_of_lt zero_le ht).ne'
  have h0 : ∀ j, (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun j => by
    rw [smul_mul_assoc, one_mul, mem_intLoc_iff_valBar]
    intro τ
    rw [valBar_smul, nnnorm_inv, inv_mul_le_iff₀ (pos_iff_ne_zero.2 ht0), mul_one]
    exact (le_absFin F v τ (u j)).trans
      ((Finset.le_sup (f := fun j => absFin F v (u j)) (Finset.mem_univ j)).trans ht.le)
  have hk : ∀ m : ℕ, ∀ j, c ^ m * (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun m => by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using h0
    | succ m ih =>
      intro j
      have := hc _ ih j
      rwa [← mul_assoc, ← pow_succ'] at this
  rw [mem_intLoc_iff_valBar]
  intro τ
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)) :=
    mul_pos (inv_pos.2 (pos_iff_ne_zero.2 ht0)) (pos_iff_ne_zero.2 hj)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)))⁻¹ hlt
  have h1 := mem_intLoc_iff_valBar.1 (hk m j) τ
  rw [mul_assoc, smul_mul_assoc, one_mul, map_mul, map_mul, map_pow, map_pow, valBar_smul, nnnorm_inv,
    ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 hm)

theorem isUnit_of_reflect {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, c * a * u j ∈ intLoc F E v) → ∀ j, a * u j ∈ intLoc F E v) : IsUnit c := by
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_left.2 fun a ha => ?_)
  refine absFin_eq_zero_iff.1 (le_antisymm ((absFin_le_iff F v).2 fun τ => ?_) zero_le)
  by_contra hne
  have hpa : 0 < valBar F v (finEmb F v τ a) := not_le.1 hne
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  have hpos : 0 < valBar F v (finEmb F v τ (a * u j)) := by
    rw [map_mul, map_mul]; exact mul_pos hpa (pos_iff_ne_zero.2 hj)
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (valBar F v (finEmb F v τ (a * u j)))⁻¹
  have h1 := mem_intLoc_iff_valBar.1
    (hc (t • a) (fun j => by rw [mul_smul_comm, ha, smul_zero, zero_mul]; exact zero_mem _) j) τ
  rw [smul_mul_assoc, valBar_smul, ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 ht)

theorem smul_mem_latLoc_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    {w l : Fin n → Fv F v ⊗[F] E} (h : l ⬝ᵥ w = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a : Fv F v ⊗[F] E, (c * a) • w ∈ latLoc F L v ↔ a • w ∈ latLoc F L v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ c • y ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := F) (Fv F v) h1
  set u := Φ.map (inclR (F := F) (Fv F v)) *ᵥ w with hu
  have hl : ∑ j, (l ᵥ* S.map (inclR (F := F) (Fv F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, hu, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, h]
  have key : ∀ a : Fv F v ⊗[F] E, a • w ∈ latLoc F L v ↔ ∀ j, a * u j ∈ intLoc F E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  simp only [key] at hc
  have hc1 := mem_intLoc_of_stable hl fun a => (hc a).2
  obtain ⟨c, rfl⟩ := isUnit_of_reflect hl fun a => (hc a).1
  have hc2 : ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v :=
    mem_intLoc_of_stable hl fun a ha => (hc _).1 fun j => by rw [Units.mul_inv_cancel_left]; exact ha j
  refine ⟨fun hy => (latLoc F L v).smul_mem ⟨_, hc1⟩ hy, fun hy => ?_⟩
  have := (latLoc F L v).smul_mem ⟨_, hc2⟩ hy
  change ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (c : Fv F v ⊗[F] E) • y ∈ _ at this
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end Local



theorem smul_mem_latV_iff : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Λ : GlobalTheory.FinPl.Lat V), Submodule.IsFullLattice D.host.E Λ → ∀ (v : GlobalTheory.FinPl.Pl D) (ε : Fin V.rank → D.host.E), ε ≠ 0 → ∀ (c : AE D) (s : Matrix (Fin V.rank) (Fin V.rank) (AE D)), IsUnit s → (∀ a ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (s) (fun i => c * (a * Formalism.L2.Theta.incA D (ε i))) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ Matrix.mulVec (s) (fun i => a * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V Λ (· = v))) → ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ c • y ∈ GlobalTheory.FinPl.latV V Λ (· = v)) := by
  intro D V Λ hΛ v ε hε c s hs h y hy
  have hfg : Λ.FG := by
    letI := hΛ
    exact Submodule.IsLattice.fg D.host.E Λ
  let π : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).comp (finPart D)
  have hπ : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ GlobalTheory.FinPl.idAt D (· = v)) →
      (z ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ (fun i => π (z i)) ∈ latLoc D.host.F Λ v) := fun z hz =>
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hfg v z hz
  let w : Fin V.rank → AE D := s *ᵥ fun i => Formalism.L2.Theta.incA D (ε i)
  have hw : ∀ a : AE D, (s *ᵥ fun i => a * Formalism.L2.Theta.incA D (ε i)) = a • w := fun a =>
    Matrix.mulVec_smul s a _
  obtain ⟨l, hl⟩ : ∃ l : Fin V.rank → AE D, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    obtain ⟨s', rfl⟩ := hs
    refine ⟨(Pi.single i (Formalism.L2.Theta.incA D (ε i)⁻¹)) ᵥ* (s'⁻¹).1, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hl' : (fun i => π (l i)) ⬝ᵥ (fun i => π (w i)) = 1 := by
    rw [← map_one π, ← hl]

    simp only [dotProduct, map_sum, map_mul]
  have hsm : ∀ (a : AE D) (z : Fin V.rank → AE D), (fun i => π ((a • z) i)) = π a • fun i => π (z i) :=
    fun a z => funext fun i => map_mul π a (z i)
  rw [hπ y hy, hπ (c • y) fun i => Ideal.mul_mem_left _ _ (hy i), hsm]
  refine smul_mem_latLoc_iff Λ hΛ hl' (fun b => ?_) _
  obtain ⟨a, ha, hab⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => b
  have hab' : π (a 0) = b := congrFun hab 0
  have h1 := h (a 0) (ha 0)
  simp only [← mul_assoc] at h1
  rw [hw, hw, hπ ((c * a 0) • w) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha 0)),
    hπ (a 0 • w) fun i => Ideal.mul_mem_right _ _ (ha 0), hsm, hsm, map_mul, hab'] at h1
  exact h1

end GlobalTheory.LineUnit

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIdealAtTStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_pair_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v)) := by
  first | exact @_root_.GlobalTheory.MiTop.line_ideal_atT_alt | exact _root_.GlobalTheory.MiTop.line_ideal_atT_alt | (intros; apply _root_.GlobalTheory.MiTop.line_ideal_atT_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixER

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop
end GlobalTheory.MiTop
theorem GlobalTheory.MiTop.tOf_fix_eR_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u f B hB a₀ a hA c
  have hId : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  set v0 : Fin (D.sp.Y 0).rank → AE D := fun i => Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩
    (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hv0
  have hv : (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = c • v0 := rfl
  rw [hv]
  set x : GA D (D.sp.Y 0) := (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) with hxdef
  set E : GA D (D.sp.Y 0) := embA B.d B.o (a₀ * a) with hEdef
  set b : GA D (D.sp.Y 0) := (show GA D (D.sp.Y 0) from f.g.b 0) with hbdef
  have hx : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) x) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId {W.S.X.eR ⟨0, hr⟩} _ rfl x ?_
    have e : iotaX W.S.X W.Q.instEq x = (1, W.S.X.xu u) := (iotaX W.S.X W.Q.instEq).apply_symm_apply _
    rw [e]
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (W.S.X.xu_fix u ⟨0, hr⟩).1
  have hE : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.eR ⟨0, hr⟩) (Or.inl (Or.inl ⟨⟨0, hr⟩, rfl⟩)) E⁻¹ ?_
    exact (B.tieH E⁻¹).1 ((embA B.d B.o).range.inv_mem ⟨a₀ * a, rfl⟩)
  have e : (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = b⁻¹ * (E⁻¹ * x) := by
    show (x⁻¹ * E * b)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  show Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹ * (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹ * Formalism.L2.Theta.mt (D.sp.Y 0) x)) (c • v0) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hE]
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixERStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_translate_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  first | exact @_root_.GlobalTheory.MiTop.tOf_fix_eR_alt | exact _root_.GlobalTheory.MiTop.tOf_fix_eR_alt | (intros; apply _root_.GlobalTheory.MiTop.tOf_fix_eR_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioStabAtT

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop

theorem centralRatio_stab_atT_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTv
  have hm : 0 < D.R.m := by have := D.R.rS_two; omega
  obtain ⟨hsd, hfr⟩ := _root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 hm
  have hFG : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := hsd.1.fg
  have hkSt : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkM : Moves (D.sp.Y 0) k ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) :=
    (GlobalTheory.StMoves.moves_iff_stabLoc _ _ hFG v k).2
      ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ _ hfr k).1 hkSt v)
  obtain ⟨c, hc⟩ := GlobalTheory.CenterScalar.center_mt_eq_smul_one D (D.sp.Y 0) z⁻¹ (Subgroup.inv_mem _ hzc)
  have hmul : ∀ g h : GA D (D.sp.Y 0), Formalism.L2.Theta.mt _ (g * h) = Formalism.L2.Theta.mt _ g * Formalism.L2.Theta.mt _ h :=
    fun g h => by simp [Formalism.L2.Theta.mt, map_mul]
  have hone : Formalism.L2.Theta.mt (D.sp.Y 0) 1 = 1 := by simp [Formalism.L2.Theta.mt, map_one]
  have h3 := _root_.GlobalTheory.T.placed_bessel_translate_vector_alt W hW hr u f B hP a₀ a hA
  have h3' := _root_.GlobalTheory.T.placed_bessel_translate_vector_alt W hW hr u' f' B' hP' a₀' a' hA'
  have h4 := _root_.GlobalTheory.T.placed_bessel_pair_vector_alt W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' v hv hTv
  have h5 := GlobalTheory.coord_first_isotropic_ne_zero W.S.X W.Q.instEq hr
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a = t at he h3
  generalize _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' = t' at he h3'
  have hunit : IsUnit (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) :=
    ⟨⟨Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹, Formalism.L2.Theta.mt (D.sp.Y 0) t', by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩, rfl⟩
  have hkey : t'⁻¹ * z⁻¹ = k * t⁻¹ := by rw [he]; group
  have hMinv : Moves (D.sp.Y 0) z⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) := by
    intro y hy
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    refine GlobalTheory.LineUnit.smul_mem_latV_iff D (D.sp.Y 0) _
      (by
        have hfull := GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd
        first | exact hfull | exact hfull.toIsLattice) v _ h5 c _ hunit ?_ y hy
    intro b hb
    have h3b := h3 b
    have h3b' := h3' b
    have h4b := h4 b hb
    generalize hw : (fun i => b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = w at h3b h3b' h4b
    have hsupp : ∀ i, w i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => by
      rw [← hw]; exact Ideal.mul_mem_right _ _ hb
    have e1 : (fun i => c * (b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w := by
      rw [← hw, hc, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
    have s1 : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) k) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t⁻¹) w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul, hkey]
    have s2 := hkM _ (GlobalTheory.FinPl.KOpen.supp_mulVec _ _ t⁻¹ hsupp)
    rw [e1, s1, ← s2, h3b, h3b']
    exact h4b
  have hM := GlobalTheory.StMoves.moves_inv hMinv
  rw [inv_inv] at hM
  exact (GlobalTheory.StMoves.moves_iff_stabLoc (D.sp.Y 0) _ hFG v z).1 hM
end GlobalTheory.MiTop
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioStabAtTStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_pair_character_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  first | exact @_root_.GlobalTheory.MiTop.centralRatio_stab_atT_alt | exact _root_.GlobalTheory.MiTop.centralRatio_stab_atT_alt | (intros; apply _root_.GlobalTheory.MiTop.centralRatio_stab_atT_alt <;> assumption)
end
end
end
