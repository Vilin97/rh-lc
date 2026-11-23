module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnity

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.USum

theorem uSame_self {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    USame ρ ρ (fun b => b) (RingHom.id Ω) := by
  let f := spMap S.R.val.toRingHom
  let P := ρ.P
  let P₀ : PolAV (Sp Ω) := {
    A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A f).1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := pull_isLB P.isLB _
    rigid := GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
    sym := GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
    ample := by
      letI := P.isAb.proper
      exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
    ktriv := by
      obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
      exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  refine ⟨P₀, pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom), pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom),
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB,
    GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, fun b => ?_⟩
  refine ⟨pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (𝟙 _) ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _⟩
  rw [Category.assoc, Over.w]; simp [f]

theorem sum_ev_shift : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω}
    (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H →
    ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H,
      ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  intro o Ω _ _ _ _ S ρ H m hm h h' e hH
  obtain ⟨P₀, a, a', x, hx, hadd⟩ := exists_isGenLab (uSame_self ρ)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨ξ₁, ⟨k₁, hk₁, hξ₁⟩, hc₁⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h rfl
  obtain ⟨ξ₂, ⟨k₂, hk₂, hξ₂⟩, hc₂⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h' e.symm
  have hξ₂0 : ξ₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk₂.ne'] at hξ₂
    exact zero_ne_one hξ₂
  refine ⟨ξ₁ * ξ₂⁻¹, ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩, fun t ht => ?_⟩
  · rw [mul_pow, inv_pow, pow_mul, hξ₁, one_pow, mul_comm k₁, pow_mul, hξ₂, one_pow, inv_one, mul_one]
  obtain ⟨v, hv⟩ := TV.ex hx hadd hm t (h := h) (κ := m • h) rfl
  have hv' := hv.transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, sub_self]) (ht _ hH)
  rw [add_sub_cancel] at hv'
  have E₁ := hc₁ t v hv
  have E₂ := hc₂ t v hv'
  simp only [RingHom.id_apply] at E₁ E₂
  have E := E₂.symm.trans E₁
  have hinv : ξ₂ * ξ₂⁻¹ = 1 := mul_inv_cancel₀ hξ₂0
  rw [← sub_eq_zero]
  refine (mul_eq_zero.1 ?_).resolve_left (mul_ne_zero hξ₂0 hx₀)
  linear_combination E - ξ₁ * S.th x₀ * (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j) * hinv

end GlobalTheory.UPoinc.USum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.theta_translate_values_shift_by_root_of_unity : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H → ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H, ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  first | exact @GlobalTheory.UPoinc.USum.sum_ev_shift | exact GlobalTheory.UPoinc.USum.sum_ev_shift | (intros; apply GlobalTheory.UPoinc.USum.sum_ev_shift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GSumEx

theorem sum_proj_shift {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (i₀ : S.J)
    {T : AddSubgroup S.Gam} (c : T →+ ZMod S.N) {h h' : S.Gam} {ξ : Ω}
    (hs : ∀ t ∈ T, ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j) :
    ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h j := by
  classical
  have key : ∀ h₀ : S.Gam, ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h₀ j =
      algebraMap o Ω (Ring.inverse (Nat.card T : o)) * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) *
        ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h₀ j := by
    intro h₀
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype]

    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum,
    Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j =
      ξ * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hs t t.2]
    ring
  rw [key h', key h, hsum]
  ring

theorem norm_val_div {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {p : ℕ} [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ M.Z) {w b ξ : Ω} {k : ℕ} (hk : 0 < k) (hξ : ξ ^ k = 1)
    (hu : ξ * w ∈ M.O (y (closedPoint _))) (hw : w ∈ M.O (y (closedPoint _))) (hb : b ∈ M.O (y (closedPoint _)))
    (hb0 : M.val y b ≠ 0) : ‖M.val y (ξ * w / b)‖ = ‖M.val y w‖ / ‖M.val y b‖ := by
  have hR := RatModel.range_eq_singleton y (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hbu : IsUnit (⟨b, hb⟩ : M.O (y (closedPoint _))) := (RatModel.val_ne_zero_iff hR _).1 hb0
  obtain ⟨hb0', hbinv⟩ := (RatModel.isUnit_O_iff _).1 hbu
  have hk' : (⟨ξ * w, hu⟩ : M.O (y (closedPoint _))) ^ k = (⟨w, hw⟩ : M.O (y (closedPoint _))) ^ k := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [mul_pow, hξ, one_mul]
  have hnorm : ‖M.val y (ξ * w)‖ = ‖M.val y w‖ := by
    have h1 := congrArg (fun x => ‖RatModel.valHomOf y _ hsp x‖) hk'
    simp only [map_pow, norm_pow, RatModel.valHomOf_apply] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hk.ne').1 h1
  have hdiv : M.val y (ξ * w / b) = M.val y (ξ * w) * M.val y b⁻¹ := by
    rw [div_eq_mul_inv]
    exact RatModel.val_mul hsp hu hbinv
  have hinv : M.val y b * M.val y b⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hb hbinv, mul_inv_cancel₀ hb0', RatModel.val_one]
  rw [hdiv, norm_mul, hnorm, eq_inv_of_mul_eq_one_right hinv, norm_inv, div_eq_mul_inv]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem norm_th_eq_delta (X : Setup F W i) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X.M.Z) {c₀ : X.Ω₁} {hc R' fg frac hth hev}
    (hR' : R' ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) (y₀ : R' →+* PadicAlgCl p)
    (hy₀ : ∀ a : R', y₀ a = X.M.val (gPt p ≫ y) a) {x₀ : X.S.Gam} (hx₀ : X.M.Div X.S.th x₀ (y (cPt p))) :
    ‖X.M.val (gPt p ≫ y) (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
  classical
  set yg := gPt p ≫ y with hyg
  have hR := RatModel.range_eq_singleton yg (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hgz : yg (closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes (M := X.M) (y := y) rfl (closedPoint (PadicAlgCl p))
  have hle : ∀ x, ‖X.M.val yg (c₀ * X.S.th x)‖ ≤ ‖X.M.val yg (c₀ * X.S.th x₀)‖ := by
    intro x
    have hq : X.S.th x / X.S.th x₀ ∈ X.M.O (y (cPt p)) := hx₀.2 x
    have hq' : X.S.th x / X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) :=
      RatModel.O_le_of_specializes hgz hq
    have hc0 : c₀ * X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
    have heq : c₀ * X.S.th x = (c₀ * X.S.th x₀) * (X.S.th x / X.S.th x₀) := by
      field_simp [hx₀.1]
    rw [heq, RatModel.val_mul hsp hc0 hq', norm_mul]
    have h1 : ‖X.M.val yg (X.S.th x / X.S.th x₀)‖ ≤ 1 := RatModel.norm_val_le_one rfl hq
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have hv : ∀ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = ‖X.M.val yg (c₀ * X.S.th x)‖ := fun x => by rw [hy₀]
  show _ = ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖
  simp only [hv]
  refine le_antisymm (le_ciSup (f := fun x => ‖X.M.val yg (c₀ * X.S.th x)‖) ⟨‖X.M.val yg (c₀ * X.S.th x₀)‖, ?_⟩ x₀) (ciSup_le hle)
  rintro _ ⟨x, rfl⟩
  exact hle x

theorem exists_lab {X₁ : Setup F W i} {ε₁} (D : Deep X₁ ε₁) {L : Type} [AddCommGroup L] [IsAddTorsionFree L]
    {yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) L} {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) L} (hC : D.Compat yy₁ yy)
    {x : D.X.S.Gam} (hx : x ∈ yy.ker) (hk : (X₁.S.r * X₁.S.N) • x = 0) : ∃ b ∈ yy₁.ker, D.lab b = x := by
  classical
  have hd1 : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    have h2 : D.m ∣ D.X.S.N := by rw [D.sq]; exact Dvd.intro_left _ (sq D.m).symm
    exact (D.dvd.trans h2).trans (Dvd.intro_left _ rfl)
  obtain ⟨d, hd⟩ := hd1
  have hpos : 0 < X₁.S.r * X₁.S.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdq : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) = d := by
    rw [hd, Nat.mul_div_cancel_left _ hpos]
  have hdpos : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne (D.X.S.r * D.X.S.N) (by rw [hd, mul_zero])

  have hcoord : ∀ j, d ∣ (x j).val := by
    intro j
    have h1 : D.X.S.r * D.X.S.N ∣ X₁.S.r * X₁.S.N * (x j).val := by
      have h0 : ((X₁.S.r * X₁.S.N) • x) j = 0 := by rw [hk]; rfl
      rw [Pi.smul_apply, nsmul_eq_mul, ← ZMod.natCast_zmod_val (x j), ← Nat.cast_mul] at h0
      exact (ZMod.natCast_eq_zero_iff _ _).1 h0
    generalize (x j).val = v at h1 ⊢
    rw [hd] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hpos h1
  let x' : D.X.S.Gam := fun j => (((x j).val / d : ℕ) : ZMod (D.X.S.r * D.X.S.N))
  have hx' : d • x' = x := by
    funext j
    simp only [x', Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hcoord j),
      ZMod.natCast_zmod_val]
  obtain ⟨a, ha⟩ := D.lab_range x'
  rw [hdq, hx'] at ha
  refine ⟨a, ?_, ha⟩
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy₁ a)
  have h1 := hC a μ hμ.symm
  rw [ha, hdq, (AddMonoidHom.mem_ker).1 hx, eq_comm, QuotientAddGroup.eq_zero_iff] at h1
  obtain ⟨ν, hν⟩ := h1
  simp only [nsmulAddMonoidHom_apply] at hν
  rw [AddMonoidHom.mem_ker, ← hμ, QuotientAddGroup.eq_zero_iff]
  refine ⟨ν, ?_⟩
  simp only [nsmulAddMonoidHom_apply]
  rw [hd, mul_comm (X₁.S.r * X₁.S.N) d, mul_nsmul] at hν
  apply eq_of_nsmul_eq_nsmul_of_addCommute hdpos (AddCommute.all _ _)
  rw [← hν]
  exact smul_comm _ _ _

private theorem isAddTorsionFree_of_free_int {X : Type} [AddCommGroup X] [Module.Free ℤ X] : IsAddTorsionFree X := by
  refine ⟨fun n hn a b hab => ?_⟩
  intro h
  let e := (Module.Free.chooseBasis ℤ X).repr
  apply e.injective
  have h1 : n • e a = n • e b := by
    rw [← map_nsmul, ← map_nsmul, h]
  exact nsmul_right_injective hn h1

private theorem rechart_proj {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω)
    (hc : c ≠ 0) (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c * S.th x ∈ R') (hev : ∀ x i, c * S.ev x i ∈ R') (T : AddSubgroup S.Gam) (cc : T →+ ZMod S.N) :
    (S.rechart c hc R' fg frac hth hev).proj T cc = S.proj T cc := rfl

private theorem mk_eq_mk_symm_of_mk_addEquiv_eq {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (χ : X) (ν : Y)
    (h : (QuotientAddGroup.mk (e χ) : ModN k Y) = QuotientAddGroup.mk ν) :
    (QuotientAddGroup.mk χ : ModN k X) = QuotientAddGroup.mk (e.symm ν) := by
  rw [QuotientAddGroup.eq] at h ⊢
  obtain ⟨β, hβ⟩ := h
  refine ⟨e.symm β, ?_⟩
  simp only [nsmulAddMonoidHom_apply] at hβ ⊢
  rw [← map_nsmul, hβ, map_add (f := _), map_neg, AddEquiv.symm_apply_apply]

private theorem ker_eq_of_addEquiv_compat {G X Y : Type} [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] (k : ℕ)
    (f : G →+ ModN k X) (f' : G →+ ModN k Y) (e : X ≃+ Y)
    (hf : ∀ a χ, f a = QuotientAddGroup.mk χ → f' a = QuotientAddGroup.mk (e χ)) : f.ker = f'.ker := by
  ext a
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (f a)
  rw [← hχ, hf a χ hχ.symm, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨e β, by rw [← hβ, map_nsmul]⟩
  · rintro ⟨β, hβ⟩
    exact ⟨e.symm β, by rw [← map_nsmul, hβ, AddEquiv.symm_apply_apply]⟩

private theorem thetaSys_proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (hT : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ (t : S.Gam) (h : t ∈ T) (h' : t ∈ T'), c ⟨t, h⟩ = c' ⟨t, h'⟩) : S.proj T c = S.proj T' c' := by
  subst hT
  congr 1
  ext t
  exact hc t t.2 t.2



theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ z₂ hq p hp c yy₁ hlab₁ y h hy yy hlab hC a ν hν hmin
  classical
  have hK1 := (isLab_onto_and_ker g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag p z₁ c yy₁ hlab₁).2
  have hK2 := (isLab_onto_and_ker g n F W Z i D.X hg hn hodd himm hE8 hTI D.proj D.ε D.diag p (y (cPt p))
    (D.lift c y h) yy hlab).2
  have hK2' : yy.ker = D.X.S.HH D.X.M z₂ := by rw [← hy]; exact hK2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, hi₀, hR', y₀, hy₀, u, l, j, hq', hyy, -⟩ := hlab
  have hint : ∀ b : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' b)‖ ≤ 1 := by
    intro b
    rw [hy₀]
    exact RatModel.norm_val_le_one (M := D.X.M) (y := y) rfl ((D.X.M.O _).algebraMap_mem b)
  have hy₀' : ∀ b : R', y₀ b = D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁) := hy₀
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL.1 hL.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hker : l.yy.ker = yy.ker := ker_eq_of_addEquiv_compat _ l.yy yy j hyy

  set ν' := j.symm ν with hν'
  have hla : l.yy a = QuotientAddGroup.mk ν' := by
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hχ]
    exact mk_eq_mk_symm_of_mk_addEquiv_eq _ j χ ν ((hyy a χ hχ.symm).symm.trans hν)
  have hlma : l.yy (D.m • a) = QuotientAddGroup.mk (D.m • ν') := by
    rw [map_nsmul, hla, ← QuotientAddGroup.mk_nsmul]

  have hmin' : ∀ χ : u.D.toPre.X, D.m • χ ≠ 0 → l.q ν' < l.q (ν' + D.m • χ) := by
    intro χ hχ
    rw [hq', hq', map_add (f := _), map_nsmul, hν', AddEquiv.apply_symm_apply]
    have hne : ν + D.m • j χ ≠ ν := by
      intro he
      apply hχ
      apply j.injective
      rw [map_nsmul, map_zero]
      simpa using he
    have hlt := hmin (ν + D.m • j χ) ⟨j χ, rfl⟩ hne
    have hsc : 0 < c.sc := CTrait.scale_pos c
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hsc
  have hk2 : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨hh, hhker, hkm, hnorm⟩ := GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint D.m (X₁.S.r * X₁.S.N) D.sq hk2 D.dvd ν' hmin'
  rw [hker] at hhker

  have := isAddTorsionFree_of_free_int (X := c.T.D.toPre.X)
  obtain ⟨b, hb, hlb⟩ := exists_lab D hC (x := D.m • hh) (yy.ker.nsmul_mem hhker _) hkm
  have hbH : b ∈ X₁.S.HH X₁.M z₁ := by rw [← hK1]; exact hb
  refine ⟨⟨b, hbH⟩, ?_⟩

  have hhH : hh ∈ D.X.S.HH D.X.M z₂ := by rw [← hK2']; exact hhker
  have hex : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab b := ⟨hh, hhH, hlb.symm⟩
  have hlift : GSum.lift D z₂ b = hex.choose := by rw [GSum.lift, dite_eq_left hex]
  obtain ⟨hH'', hm''⟩ := hex.choose_spec
  obtain ⟨ξ, ⟨k', hk'pos, hξ⟩, hshift⟩ := GlobalTheory.T.theta_translate_values_shift_by_root_of_unity D.X.ρ (D.X.S.HH D.X.M z₂) D.m D.sq hh hex.choose
    (by rw [hm'', hlb]) ((D.X.S.HH D.X.M z₂).sub_mem hH'' hhH)
  have hsh := sum_proj_shift (S := D.X.S) D.X.ρ.i₀ (T := D.X.S.TT D.X.M z₂) (GSum.wtChar D _ a) hshift

  have hne : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  have hbase : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hqz : D.q (y (cPt p)) = z₁ := by
    rw [← c.cen, ← h]
    rfl
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ (GSum.base X₁ z₁) hbase
    (y (cPt p)) hqz
  have hth0 := norm_th_eq_delta D.X y (hth := hth) (hev := hev) (hc := hc) (fg := fg) (frac := frac) hR' y₀ hy₀ hx₀
  set x₀ := D.lab (GSum.base X₁ z₁) with hx₀def
  set T := D.X.S.TT D.X.M z₂ with hT
  set wc := GSum.wtChar D T a with hwc
  set Sm := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev hh j with hSm
  have hmem : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j =
      ((∑ j, algebraMap D.X.o₁ R' (D.X.S.proj T wc j D.X.ρ.i₀) * (⟨c₀ * D.X.S.ev h₀ j, hev h₀ j⟩ : R') : R') :
        D.X.Ω₁) := by
    intro h₀
    simp only [Finset.mul_sum, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmemO : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j ∈
      D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := fun h₀ => by
    rw [hmem h₀]
    exact hR' (Subtype.property _)
  have hpart : GSum.part D z₁ z₂ a ⟨b, hbH⟩ = ξ * (c₀ * Sm) / (c₀ * D.X.S.th x₀) := by
    rw [GSum.part]
    try dsimp only
    rw [hlift, hsh, mul_left_comm ξ c₀ Sm, mul_div_mul_left _ _ hc]
  have hw : ξ * (c₀ * Sm) ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := by
    have := hmemO hex.choose
    rw [hsh] at this
    rw [← mul_assoc, mul_comm ξ c₀, mul_assoc]
    exact this
  have hthO : c₀ * D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
  have hthne : D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hth0
    exact hδ.ne' hth0.symm
  have e1 : D.X.S.proj T wc = D.X.S.proj (D.X.S.perp l.yy.ker) (l.wt (D.m • ν')) := by
    refine thetaSys_proj_congr _ (by rw [hT, ThetaSys.TT, hker, hK2']) _ _ fun t ht ht' => ?_
    exact Eq.trans rfl (l.wt_eq (D.m • a) (D.m • ν') hlma ⟨t, ht'⟩).symm
  have hSmn : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sm)‖ = (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ * Real.exp (-l.q ν') := by
    have e1' : D.X.S.proj T wc =
        (D.X.S.rechart c₀ hc R' fg frac hth hev).proj ((D.X.S.rechart c₀ hc R' fg frac hth hev).perp l.yy.ker)
          (l.wt (D.m • ν')) := by
      rw [rechart_proj]
      exact e1
    rw [← e1', hi₀] at hnorm

    rw [← hnorm, hSm, hmem hh, ← hy₀', map_sum]
    simp only [map_mul]
  rw [hpart, norm_val_div (M := D.X.M) (gPt p ≫ y) hk'pos hξ hw (hmemO hh) hthO hthne, hSmn, hth0,
    mul_div_cancel_left₀ _ hδ.ne', hq', hν', AddEquiv.apply_symm_apply]
  try rfl

end GlobalTheory.Poinc.GSumEx
end
end
end
