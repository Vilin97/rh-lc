module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelicStatement
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorInvCentralFlipInvariantFormEq

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.FlipScalStep

def flipInv {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * incA D ((m : D.host.E)⁻¹) + cA D e * (m : AE D) + (1 - e - cA D e)

theorem flipElt_mul_flipInv {D : D7} {e : AE D} (he : IsSplitIdem D e) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * flipInv e m = 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]
  unfold flipElt flipInv
  linear_combination (e + cA D e) * hinc
    + ((m : AE D) * incA D ((m : D.host.E)⁻¹) - m - incA D ((m : D.host.E)⁻¹) + 1) * (hee + hcc)
    + ((m : AE D) ^ 2 - 2 * m + incA D ((m : D.host.E)⁻¹) ^ 2 - 2 * incA D ((m : D.host.E)⁻¹) + 2) * hec

theorem mt_inv_eq {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.mt V g⁻¹ = flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hmul : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hfb : (flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) *
      (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, flipElt_mul_flipInv he hm, one_smul]
  calc Formalism.L2.Theta.mt V g⁻¹ = Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g *
        (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))) := by rw [hg, hfb, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hmul, Matrix.one_mul]

theorem mul_flipInv_sub {D : D7} {e : AE D} (he : IsSplitIdem D e) (m : ℕ) :
    (e + cA D e) * (flipInv e m - 1) = flipInv e m - 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  unfold flipInv
  linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hcc
    + ((m : AE D) + incA D ((m : D.host.E)⁻¹) - 2) * hec

theorem idem_mul_flipInv_pow {D : D7} {e : AE D} (he : IsSplitIdem D e) (m n : ℕ) :
    e * flipInv e m ^ n = e * incA D ((m : D.host.E)⁻¹) ^ n := by
  obtain ⟨hee, hec, -⟩ := he
  have heb : e * flipInv e m = e * incA D ((m : D.host.E)⁻¹) := by
    unfold flipInv
    linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hec
  induction n with
  | zero => rfl
  | succ n ih =>
    linear_combination flipInv e m * ih + incA D ((m : D.host.E)⁻¹) ^ n * heb

theorem suppAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.SuppAt e V g⁻¹ := by
  intro i j
  rw [mt_inv_eq V g e he hm hg, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc (e + cA D e) * (flipInv e m * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      = ((e + cA D e) * (flipInv e m - 1)) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by ring
    _ = _ := by rw [mul_flipInv_sub he m]; ring

theorem isDetAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    {x : (AE D)ˣ} (hx : IsFlipDet V e m x) : Formalism.L2.Theta.IsDetAt e V g⁻¹ x := by
  unfold Formalism.L2.Theta.IsDetAt
  rw [mt_inv_eq V g e he hm hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    idem_mul_flipInv_pow he m]
  unfold IsFlipDet at hx
  have hee := he.1
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ hmE, map_one]
  have hpow : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
    rw [← mul_pow, hinc, one_pow]
  have hy : (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1 := by
    linear_combination (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hee + e ^ 2 * hpow
  linear_combination (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * hx - (x : AE D) * hy

theorem om_inv_flip_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW P e m g x ℓ hP hm hg hx hℓ
  have he : IsSplitIdem D e := hP.1
  have hm1 : Formalism.L2.Theta.mt W (1 : GA D W) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : Formalism.L2.Theta.SuppAt e W 1 := fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]
  have h1' : Formalism.L2.Theta.IsDetAt e W 1 1 := by
    unfold Formalism.L2.Theta.IsDetAt
    rw [hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]
  obtain ⟨r, hr, H⟩ := hW.om_split e he g⁻¹ 1 (suppAt_inv V g e he hm hg) h1 x 1 (isDetAt_inv V g e he hm hg hx) h1'
  refine ⟨r, hr, fun f hf => ?_⟩
  rw [H ℓ (fun u hu f hf => hℓ u hu f hf) f hf, splitFacO, map_one, mul_one, Circle.coe_inv]

end GlobalTheory.LevelSeries.FlipScalStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorInvCentralFlipInvariantFormEqStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | exact GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | (intros; apply GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhase

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem cflip_flipElt_add {a b : AE D} (m : ℕ) (h1 : a * b = 0) (h2 : a * cA D b = 0) (h3 : cA D a * b = 0)
    (h4 : cA D a * cA D b = 0) : flipElt (a + b) m = flipElt a m * flipElt b m := by
  unfold flipElt
  rw [map_add (f := _)]
  linear_combination (-((m : AE D) - 1) ^ 2) * h1 - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h2
    - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h3 - (incA D ((m : D.host.E)⁻¹) - 1) ^ 2 * h4

theorem cflip_sum_idem {S : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) : (∑ PP ∈ S, es PP) * (∑ PP ∈ S, es PP) = ∑ PP ∈ S, es PP := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun PP hPP => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · exact (hes PP hPP).1.1
  · intro Q hQ hne
    exact GlobalTheory.Tow.idemAt_orth (hes PP hPP) (hes Q hQ) (Ne.symm hne)

theorem cflip_mul_cA_eq_zero {e u v : AE D} (he : e * cA D e = 0) (hu : e * u = u) (hv : e * v = v) : u * cA D v = 0 := by
  rw [← hu, ← hv, map_mul]
  linear_combination (u * cA D v) * he

theorem cflip_isHalf_mono {m n : ℕ} {e u : AE D} (hu : e * u = u) {y : Mx D m n} (hy : Formalism.IndefR.Datum.IsHalf (cA D u) y) :
    Formalism.IndefR.Datum.IsHalf (cA D e) y := by
  intro i j
  rw [← hy i j, ← mul_assoc, ← map_mul, hu]

theorem cflip_det_split {R : Type*} [CommRing R] {a b t x : R} (hab : a * b = 0)
    (hx : x * ((a + b) * t + (1 - (a + b))) = 1) : x * ((a * t + (1 - a)) * (b * t + (1 - b))) = 1 := by
  linear_combination hx + (x * (t - 1) ^ 2) * hab

theorem cflip_smul_one_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c d : R)
    (X : Matrix n n R) : ((c * d) • (1 : Matrix n n R)) * X = c • ((d • (1 : Matrix n n R)) * X) := by
  rw [mul_smul, Matrix.smul_mul]

theorem cflip_unit_split {R : Type*} [CommRing R] {x u v : R} (h : x * (u * v) = 1) : x = x * v * (x * u) := by
  linear_combination (-x) * h


theorem centralFlip_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW T
  induction T using Finset.induction_on with
  | empty =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, -, he⟩, -⟩ := hS
    rw [Finset.sum_empty] at he
    subst he
    have h1 : flipElt (0 : AE D) m = 1 := by unfold flipElt; simp
    have hz1 : z = 1 := GlobalTheory.IdemSupport.mt_inj V (by rw [hz, h1, one_smul, GlobalTheory.IdemSupport.mt_one])
    have hx1 : x = 1 := by simpa [IsFlipDet] using hx
    subst hz1 hx1
    refine ⟨1, one_pos, fun f hf => ?_⟩
    simp only [inv_one, Circle.coe_one, map_one, inv_one, Complex.ofReal_one, one_mul]
    show ℓ ((om 1) f) = ℓ f
    rw [map_one]
    rfl
  | @insert P T' hP ih =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, hes, heT⟩, hT⟩ := hS
    have hesP := hes P (Finset.mem_insert_self P T')
    have hes' : ∀ Q ∈ T', Formalism.L2.NTheta.IsIdemAt (es Q) Q := fun Q hQ => hes Q (Finset.mem_insert_of_mem hQ)
    have heT' : eT = es P + ∑ Q ∈ T', es Q := by rw [heT, Finset.sum_insert hP]
    have hab : es P * ∑ Q ∈ T', es Q = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun Q hQ => GlobalTheory.Tow.idemAt_orth hesP (hes' Q hQ) (fun h => hP (h ▸ hQ))
    have hbb := cflip_sum_idem hes'
    have heA : eT * es P = es P := by
      rw [heT', add_mul, hesP.1.1, mul_comm, hab, add_zero]
    have heB : eT * ∑ Q ∈ T', es Q = ∑ Q ∈ T', es Q := by
      rw [heT', add_mul, hab, hbb, zero_add]
    have hSa : IsIdemSum (es P) {P} :=
      ⟨⟨es, by simpa using hesP, by simp⟩, cflip_mul_cA_eq_zero hT heA heA⟩
    have hSb : IsIdemSum (∑ Q ∈ T', es Q) T' := ⟨⟨es, hes', rfl⟩, cflip_mul_cA_eq_zero hT heB heB⟩
    have hflip : flipElt eT m = flipElt (es P) m * flipElt (∑ Q ∈ T', es Q) m := by
      rw [heT']
      refine cflip_flipElt_add m hab (cflip_mul_cA_eq_zero hT heA heB) ?_ (by rw [← map_mul, hab, map_zero])
      rw [mul_comm]
      exact cflip_mul_cA_eq_zero hT heB heA
    obtain ⟨zP, -, -, hzP⟩ := GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic D V {P} m (es P) hSa hm

    have h1 : Formalism.L2.Theta.mt V zP * Formalism.L2.Theta.mt V zP⁻¹ = 1 := by
      rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one]
    have hz' : Formalism.L2.Theta.mt V (z * zP⁻¹) =
        flipElt (∑ Q ∈ T', es Q) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
      rw [hzP] at h1
      calc Formalism.L2.Theta.mt V (z * zP⁻¹)
          = (flipElt (∑ Q ∈ T', es Q) m * flipElt (es P) m) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹ := by
            rw [GlobalTheory.IdemSupport.mt_mul, hz, hflip, mul_comm (flipElt (es P) m)]
        _ = flipElt (∑ Q ∈ T', es Q) m • (flipElt (es P) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹) := cflip_smul_one_mul _ _ _
        _ = _ := by rw [h1]

    have hx0 : (x : AE D) * ((es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q))) = 1 := by
      rw [heT'] at hx
      exact cflip_det_split hab hx
    have hxa : (x : AE D) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) * (es P * (m : AE D) ^ V.rank + (1 - es P)) = 1 := by
      rw [mul_assoc, mul_comm ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + _)]; exact hx0
    have hxb : (x : AE D) * (es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) = 1 := by
      rw [mul_assoc]; exact hx0
    let xa : (AE D)ˣ := ⟨_, _, hxa, by rw [mul_comm]; exact hxa⟩
    let xb : (AE D)ˣ := ⟨_, _, hxb, by rw [mul_comm]; exact hxb⟩
    have hxx : x = xa * xb := by
      apply Units.ext
      simp only [xa, xb, Units.val_mul]
      exact cflip_unit_split hx0
    have hxaD : IsFlipDet V (es P) m xa := hxa
    have hxbD : IsFlipDet V (∑ Q ∈ T', es Q) m xb := hxb
    obtain ⟨rP, hrP, hPstep⟩ := GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq D ψ V W χV χW om hW P (es P) m zP xa ℓ hesP hm hzP hxaD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heA hy) φ hφ)
    obtain ⟨r', hr', hrest⟩ := ih (∑ Q ∈ T', es Q) m (z * zP⁻¹) xb ℓ hSb hm hz' hxbD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heB hy) φ hφ)
    refine ⟨rP * r', mul_pos hrP hr', fun f hf => ?_⟩
    have hsplit : ((z⁻¹ : GA D V), (1 : GA D W)) = (zP⁻¹, 1) * ((z * zP⁻¹)⁻¹, 1) := by
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hPstep _ (hW.om_pres _ _ hf), hrest f hf, hxx, map_mul]
    push_cast
    ring

end GlobalTheory.LevelSeries

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhaseStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.centralFlip_phase | exact GlobalTheory.LevelSeries.centralFlip_phase | (intros; apply GlobalTheory.LevelSeries.centralFlip_phase <;> assumption)
end
end
