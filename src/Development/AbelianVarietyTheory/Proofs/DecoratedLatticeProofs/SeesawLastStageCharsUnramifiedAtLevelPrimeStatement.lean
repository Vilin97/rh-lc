module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
public import Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum
public import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.WeilDatumUniqueOfDeterminants

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

end Scalar

section Side

end Side

end Formalism.IndefR.flipTwoThree

end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

variable {D : D7}

abbrev sigE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sigE_sigE (a : D.host.E) : sigE D (sigE D a) = a := star_star a

theorem gram_herm (V : HSp D) (i j : Fin V.rank) : sigE D (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem cA_incA' (a : D.host.E) : cA D (incA D a) = incA D (sigE D a) := by
  simp [cA, incA, sigR, inclR]

theorem gramA_herm (V : HSp D) (i j : Fin V.rank) :
    cA D (V.gram.map (incA D) i j) = V.gram.map (incA D) j i := by
  simp only [Matrix.map_apply, cA_incA', gram_herm]

def mkGA (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) : GA D V :=
  let g : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨Matrix.nonsingInvUnit M hd, hM⟩
  g

theorem aniso_data (V : HSp D) (hn : 0 < V.rank) :
    ∃ (u : Fin V.rank → D.host.E) (ainv : D.host.E), ainv * hsq (sigE D) V.gram u = 1 ∧ sigE D ainv = ainv := by
  have : Nonempty (Fin V.rank) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := exists_aniso (sigE D) sigE_sigE V.gram (gram_herm V) (gram_det_ne V)
  refine ⟨u, (hsq (sigE D) V.gram u)⁻¹, inv_mul_cancel₀ hu, ?_⟩
  rw [map_inv₀, sigma_hsq (sigE D) sigE_sigE V.gram (gram_herm V) u]

theorem exists_GA_det (V : HSp D) (hn : 0 < V.rank) (x : AE D) (hx : cA D x * x = 1) (hxu : IsUnit x) :
    ∃ (R : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (g : GA D V), mt V g = 1 + (x - 1) • R ∧ (mt V g).det = x := by
  obtain ⟨u, ainv, ha, hainv⟩ := aniso_data V hn
  have haA : incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
    rw [← hsq_map (incA D) (sigE D) (cA D) (fun a => (cA_incA' a).symm), ← map_mul, ha, map_one]
  have hainvA : cA D (incA D ainv) = incA D ainv := by rw [cA_incA', hainv]
  set R := proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)
  have hM := proj_unitary (cA D) cA_cA (V.gram.map (incA D)) (gramA_herm V) (fun i => incA D (u i))
    (incA D ainv) haA hainvA x hx
  have hdet := det_proj' (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv) haA x
  exact ⟨R, mkGA V _ hM (by rw [hdet]; exact hxu), rfl, hdet⟩

theorem splitDet : SplitDetP := by
  intro D V hn e he x hx hsupp
  obtain ⟨R, g, hg, hdet⟩ := exists_GA_det V hn (x : AE D) (by rw [mul_comm]; exact hx) x.isUnit
  refine ⟨g, ?_, ?_, hdet⟩
  · intro i j
    rw [hg, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    unfold SuppAtU at hsupp
    rw [hsupp]
  · have hxi : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := x.mul_inv
    set xi : AE D := ((x⁻¹ : (AE D)ˣ) : AE D) with hxi_def
    set x0 : AE D := (x : AE D) with hx0
    have p1 : (e * x0 + (1 - e)) * (e * xi + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    have p2 : (e * xi + (1 - e)) * (e * x0 + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    obtain ⟨y, hy⟩ : ∃ y : (AE D)ˣ, (y : AE D) = e * x0 + (1 - e) := ⟨⟨_, _, p1, p2⟩, rfl⟩
    refine ⟨y, ?_⟩
    unfold IsDetAt
    rw [hy, hdet]

end Formalism.IndefR.flipTwoThree

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitP

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharsFromWeil

section Alg

variable {R : Type*} [CommRing R]

theorem alg_key (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) (hab : a * b = 1) :
    (e * a + c e * c b + (1 - e - c e)) * (e * b + c e * c a + (1 - e - c e)) = 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  have hcab : c a * c b = 1 := by rw [← map_mul, hab, map_one]
  linear_combination e * e * hab + c e * c e * hcab +
    (a * c a + c b * b - a - b - c b - c a + 2) * hec + (2 - a - b) * he1 + (2 - c b - c a) * hce

theorem alg_conj (c : R →+* R) (hcc : ∀ z, c (c z) = z) (e a b : R) :
    c (e * a + c e * c b + (1 - e - c e)) = e * b + c e * c a + (1 - e - c e) := by
  simp only [map_add (f := _), map_mul, map_sub, map_one, hcc]
  ring

theorem alg_supp (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    (e + c e) * ((e * a + c e * c b + (1 - e - c e)) - 1) = (e * a + c e * c b + (1 - e - c e)) - 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  linear_combination (a - 1) * he1 + (c b - 1) * hce + (c b + a - 2) * hec

theorem alg_at (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    e * (e * a + c e * c b + (1 - e - c e)) + (1 - e) = e * a + (1 - e) := by
  linear_combination (a - 1) * he1 + (c b - 1) * hec

theorem alg_prod {e f E x : R} (hef : e * f = 0) (hsum : e + f = E) (hsupp : E * (x - 1) = x - 1) :
    x = (e * x + (1 - e)) * (f * x + (1 - f)) := by
  linear_combination (-(x - 1) ^ 2) * hef - (x - 1) * hsum - hsupp

end Alg

variable {D : D7}

theorem splitFac_eq {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) {e : AE D} (he : IsSplitIdem D e)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) :
    splitFacO χS χT x y = splitFacO χS' χT' x y := by
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [h2 ℓ hℓ f hf] at e1
  have e2 : (r' : ℂ) * (splitFacO χS' χT' x y : ℂ) = r * (splitFacO χS χT x y : ℂ) :=
    mul_right_cancel₀ hne e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr'.ne') e2).symm

theorem exists_unit_idem {e : AE D} (he : e * e = e) (u : (AE D)ˣ) : ∃ x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) := by
  have hu : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk : (e * u + (1 - e)) * (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) = 1 := by
    linear_combination (2 - (u : AE D) - ((u⁻¹ : (AE D)ˣ) : AE D)) * he + e * e * hu
  exact ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, rfl⟩

theorem isSplitIdem_conj' {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
    by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  change (1 : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
  rw [Formalism.IndefR.flipTwoThree.mt_one', Matrix.det_one]
  ring

theorem exists_detUnit {e : AE D} (he : IsSplitIdem D e) (u : (AE D)ˣ) :
    ∃ X : (AE D)ˣ, (X : AE D) * cA D (X : AE D) = 1 ∧ Formalism.IndefR.InjectiveDecompositionAction.SuppAtU D e X ∧
      e * (X : AE D) + (1 - e) = e * u + (1 - e) := by
  have hab : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk := alg_key (cA D) he.1 he.2.1 hab
  refine ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, ?_, alg_supp (cA D) he.1 he.2.1, alg_at (cA D) he.1 he.2.1⟩
  change _ * cA D _ = 1
  rw [alg_conj (cA D) Formalism.L2.Theta.cA_cA]
  exact hk

theorem chiT_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hS : 0 < S.rank) {e : AE D}
    (he : IsSplitIdem D e) (u x : (AE D)ˣ) (hx : (x : AE D) = e * u + (1 - e)) : χT x = χT' x := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨g, hg, ⟨x', hx'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D S hS e he X hX1 hX2
  have h0 : (x' : AE D) = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := hx'
  have hxx : x' = x := Units.ext (by rw [h0, hdet, hX3, hx])
  subst hxx
  have := splitFac_eq H H' he hg (GlobalTheory.WeilDetermined.suppAt_one e T) hx' (isDetAt_one e T)
  simpa only [splitFacO, map_one, mul_one, _root_.inv_inj] using this

theorem chiS_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hT : 0 < T.rank) {e : AE D}
    (he : IsSplitIdem D e) (u y : (AE D)ˣ) (hy : (y : AE D) = e * u + (1 - e)) : χS y = χS' y := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨h, hh, ⟨y', hy'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D T hT e he X hX1 hX2
  have h0 : (y' : AE D) = e * (Formalism.L2.Theta.mt T h).det + (1 - e) := hy'
  have hyy : y' = y := Units.ext (by rw [h0, hdet, hX3, hy])
  subst hyy
  have := splitFac_eq H H' he (GlobalTheory.WeilDetermined.suppAt_one e S) hh (isDetAt_one e S) hy'
  simpa only [splitFacO, map_one, inv_one, one_mul] using this

theorem eq_of_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (x : (AE D)ˣ) (h1 : infPart D (x : AE D) = 1)
    (h2 : ∀ w, w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (x : AE D)) = 1) : χ x = χ' x := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp : algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 :=
    (GlobalTheory.VacStabFixed.supp_iff hε _).2 ⟨by rw [map_sub, map_one, h1, sub_self],
      fun w hw => by rw [map_sub, map_sub, map_one, map_one, h2 w hw, sub_self]⟩
  have he : IsSplitIdem D p.e := p.split
  have hce : IsSplitIdem D (cA D p.e) := isSplitIdem_conj' he
  obtain ⟨x1, hx1⟩ := exists_unit_idem he.1 x
  obtain ⟨x2, hx2⟩ := exists_unit_idem hce.1 x
  have hprod : x = x1 * x2 := by
    apply Units.ext
    rw [Units.val_mul, hx1, hx2]
    exact alg_prod he.2.1 hsum hsupp
  rw [hprod, map_mul, map_mul, hag p.e he x x1 hx1, hag _ hce x x2 hx2]

theorem charUnram_transfer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ' p.v := by
  intro x h1 h2 h3 h4
  rw [← eq_of_comp p χ χ' hag x h1 h2]
  exact h x h1 h2 h3 h4

theorem charUnram_of_weil : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  intro D k _ _ _ _ p ψ S T χS χT χS' χT' om H H'
  exact ⟨fun hS => charUnram_transfer p χT χT' fun e he u x hx => chiT_agree H H' hS he u x hx,
    fun hT => charUnram_transfer p χS χS' fun e he u y hy => chiS_agree H H' hT he u y hy⟩

end GlobalTheory.CharsFromWeil

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitPStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  first | exact @GlobalTheory.CharsFromWeil.charUnram_of_weil | exact GlobalTheory.CharsFromWeil.charUnram_of_weil | (intros; apply GlobalTheory.CharsFromWeil.charUnram_of_weil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  first | exact @GlobalTheory.LastStep.chars_unram | exact GlobalTheory.LastStep.chars_unram | (intros; apply GlobalTheory.LastStep.chars_unram <;> assumption)
end
end
