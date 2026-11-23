module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFilStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizer

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.FlatKummer

theorem isPrimitiveRoot_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (ζ m) (l ^ m) := by
  have hp : ∀ k, ζ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  have h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  cases m with
  | zero => simp [h0]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem exists_exponent_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (z w : ℕ → Ω) (hz : ∀ m, z (m + 1) ^ l = z m)
    (hw : ∀ m, w (m + 1) ^ l = w m) (hwz : w 0 = z 0) :
    ∃ c : ℤ_[l], ∀ m, w m = ζ m ^ (PadicInt.toZModPow m c).val * z m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0 := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, hx, ih]
  by_cases hz0 : z 0 = 0
  · refine ⟨0, fun m => ?_⟩
    have a : z m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)
    have b : w m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1
      ((hiter w hw m).trans (hwz.trans hz0))
    rw [a, b, mul_zero]
  have hzm : ∀ m, z m ≠ 0 := fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])
  have hprim := isPrimitiveRoot_of_seq l ζ h0 hs h1
  have hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
    intro m a b
    have hf : IsOfFinOrder (ζ m) := (hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m := by
    intro m
    obtain ⟨a, -, ha⟩ := (hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by
      rw [div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩
  choose a ha using e1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [mul_pow, hw, hz] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i] at h2
    have h3 := (hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [hpow]
  simp

theorem rootT_succ_pow_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (m : ℕ) : rootT e (m + 1) ^ l = rootT e m := by
  rw [rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem exists_kummer_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  intro l _ K bk C
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose z hz using hz
  have hinj : Function.Injective (algebraMap (Om l) ℂ_[l]) := (algebraMap (Om l) ℂ_[l]).injective
  have hz' : ∀ n, ((rootT bk.flat n : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := hz
  have hzs : ∀ m, z (m + 1) ^ l = z m := by
    intro m
    apply hinj
    rw [map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]
    push_cast
    rfl
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have hθ : rootT bk.flat 0 = intToOC K r := by
    show bk.flat.untilt = _
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  have hz0 : z 0 = (((r : ↥K.1) : Om l)) := by
    apply hinj
    rw [← hz', hθ, coe_intToOC]
    rfl
  have good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m := by
    intro g
    have hfix : (g : GQ l) (z 0) = z 0 := by
      rw [hz0]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2
    obtain ⟨c, hc⟩ := exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs
      (fun m => by rw [← map_pow, hzs]) hfix
    refine ⟨c, fun m => ?_⟩
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF (g : GQ l) bk.flat) =
        Per.σF (g : GQ l) (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : rootT (Per.σF (g : GQ l) bk.flat) m = Per.σO (g : GQ l) (rootT bk.flat m) := by
      rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
    rw [hsig]
    apply Subtype.ext
    have h1 : ((Per.σO (g : GQ l) (rootT bk.flat m) : Per.OC l) : ℂ_[l]) = Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l]) :=
      by apply GlobalTheory.RingIface.sigO_coe
    have h2 : Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      GlobalTheory.RingBasics.σC_coe (g : GQ l) _
    push_cast
    rw [h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]
  classical
  refine ⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩
  by_cases hg : bk.FixFlat g
  · simp only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [show Per.σF (g : GQ l) bk.flat = bk.flat from hg]
  · simp only [hg, if_false]
    exact (good g).choose_spec m

end GlobalTheory.FlatKummer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  first | (exact @GlobalTheory.FlatKummer.exists_kummer_flat) | (exact GlobalTheory.FlatKummer.exists_kummer_flat) | (intros; apply GlobalTheory.FlatKummer.exists_kummer_flat  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriods

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogFlat

theorem rootT_cocycle_of_pow_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (g : GQ l) (y ϖ x : Per.Fl l) (n : ℕ) (a b : ℤ_[l]),
    y ^ n = ϖ * x → ϖ.untilt ≠ 0 →
    (∀ m, rootT (Per.σF g y) m = rootT C.ε m ^ (PadicInt.toZModPow m a).val * rootT y m) →
    (∀ m, rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m b).val * rootT ϖ m) →
    ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val * rootT x m := by
  intro l _ C g y ϖ x n a b hyx hϖ ha hb m
  have hmul : ∀ u v : Per.Fl l, rootT (u * v) m = rootT u m * rootT v m := by
    intro u v; simp only [rootT, iterate_map_mul, map_mul]
  have hpow : ∀ u : Per.Fl l, rootT (u ^ n) m = rootT u m ^ n := by
    intro u; simp only [rootT, iterate_map_pow, map_pow]
  have hζ : rootT C.ε m ^ (l ^ m) = 1 := by
    rw [rootT_pow_eq_untilt]; exact (core_isEps l C).1
  have hϖm : rootT ϖ m ≠ 0 := by
    intro h0; apply hϖ; rw [← rootT_pow_eq_untilt, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hζ0 : ∀ k : ℕ, rootT C.ε m ^ k ≠ 0 := by
    intro k h0
    have : rootT C.ε m = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rw [this, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
    exact zero_ne_one hζ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set A := (PadicInt.toZModPow m a).val
  set B := (PadicInt.toZModPow m b).val
  set Cc := (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val
  have hexp : rootT C.ε m ^ (n * A) = rootT C.ε m ^ (B + Cc) := by
    rw [pow_eq_pow_mod (n * A) hζ, pow_eq_pow_mod (B + Cc) hζ]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    simp only [A, B, Cc, Nat.cast_mul, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, map_sub, map_mul,
      map_natCast]
    ring
  have h1 : rootT ((Per.σF g y) ^ n) m = rootT (Per.σF g ϖ * Per.σF g x) m := by
    rw [← map_pow, ← map_mul, hyx]
  rw [hpow, hmul, ha, hb, mul_pow, ← pow_mul, ← hpow y, hyx, hmul, mul_comm A n, hexp] at h1
  have h2 : rootT C.ε m ^ B * (rootT ϖ m * rootT ((Per.σF g) x) m) =
      rootT C.ε m ^ B * (rootT ϖ m * (rootT C.ε m ^ Cc * rootT x m)) := by
    rw [pow_add] at h1; linear_combination -h1
  have h3 := mul_left_cancel₀ (hζ0 B) h2
  exact mul_left_cancel₀ hϖm h3

theorem rootT_σF_tilt_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (C : Core l), C.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
    (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ∀ (g : GQ l) (m : ℕ),
    rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m (kummer P g)).val * rootT ϖ m := by
  intro l _ P C hζ ϖ hr g m
  have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g ϖ) =
      Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] ϖ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
  have hsig : rootT (Per.σF g ϖ) m = Per.σO g (rootT ϖ m) := by
    rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
  rw [hsig]
  apply Subtype.ext
  have h1 : ((Per.σO g (rootT ϖ m) : Per.OC l) : ℂ_[l]) = Per.σC g (rootT ϖ m : ℂ_[l]) :=
    GlobalTheory.RingIface.sigO_coe l g _
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (lRoot l m)) = algebraMap (Om l) ℂ_[l] (g (lRoot l m)) :=
    GlobalTheory.RingBasics.σC_coe g _
  push_cast
  rw [h1, hr, h2, isKummer_kummer P g m, map_mul, map_pow, C.ε_root, hζ]

theorem exists_log_flat_pow_Bst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF _
  obtain ⟨ϖ, hr⟩ := GlobalTheory.Pst.NoLog.exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨x, hxu, hx⟩ := GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit l K bk ϖ hϖ
  obtain ⟨cπ, hcπ, hfix⟩ := GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer l K bk C
  obtain ⟨bx, hφ, hgal⟩ := GlobalTheory.T.exists_teichmuller_log_unit_bcris l C x hxu
  have hϖ0 : ϖ.untilt ≠ 0 := by
    rw [hϖ]; exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨T.eB.symm bx, fun g => (bk.Ep.natDegree : ℤ_[l]) * cπ g, ⟨fun g => ?_, ?_⟩,
    fun g hg => by simp [hfix g hg], GlobalTheory.T.exists_truncLog_gal_mod_filP l K bk C cπ hcπ⟩
  · have hx' := rootT_cocycle_of_pow_eq_mul l C (g : GQ l) bk.flat ϖ x bk.Ep.natDegree (cπ g) (kummer P g) hx hϖ0 (hcπ g)
      (rootT_σF_tilt_l l P C hF.ζ ϖ hr g)
    have h1 := hgal (g : GQ l) _ hx'
    have h2 : P.actQ (g : GQ l) (T.eB.symm bx) = T.eB.symm bx +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      apply T.eB.injective
      rw [T.actB, RingEquiv.apply_symm_apply, h1, map_add (f := _), RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
        T.zB, hF.t]
    rw [map_add (f := _), actSt_X, actSt_C, h2, Polynomial.C_add]
    have key : ((kummer P (g : GQ l) : ℤ_[l]) : ℚ_[l]) • P.tB +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB =
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      rw [← add_smul]; congr 1; push_cast; ring
    show _ = _ + Polynomial.C ((((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB)
    rw [← key, Polynomial.C_add]; ring
  · have h2 : P.φB (T.eB.symm bx) = (l : P.R.B) * T.eB.symm bx := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    rw [map_add (f := _), phiSt_X, phiSt_C, h2, mul_add, Polynomial.C_mul, map_natCast]

end GlobalTheory.LogFlat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriodsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.LogFlat.exists_log_flat_pow_Bst) | (exact GlobalTheory.LogFlat.exists_log_flat_pow_Bst) | (intros; apply GlobalTheory.LogFlat.exists_log_flat_pow_Bst  <;> assumption)
end
end
